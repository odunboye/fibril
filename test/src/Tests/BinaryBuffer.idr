module Tests.BinaryBuffer

import Data.Buffer
import Data.IORef
import Data.List
import Fibril.Data.Bytes
import Fibril.Runtime.Binary

%default total

data ReadStep = Supply (List Bits8) Bool Bool | Claim Int Bool Bool

fill : Buffer -> Int -> List Bits8 -> IO ()
fill buffer offset [] = pure ()
fill buffer offset (byte :: rest) = do
  setBits8 buffer offset byte
  fill buffer (offset + 1) rest

scriptRead : IORef (List ReadStep) -> Buffer -> Int -> Int -> IO BufferRead
scriptRead script buffer offset remaining = do
  steps <- readIORef script
  case steps of
    [] => pure (ReadBlock 0 False True)
    Supply bytes failed eof :: rest => do
      writeIORef script rest
      if length bytes > cast remaining then pure (ReadBlock (-1) True False) else do
        fill buffer offset bytes
        pure (ReadBlock (cast (length bytes)) failed eof)
    Claim count failed eof :: rest => do
      writeIORef script rest
      pure (ReadBlock count failed eof)

capture : Nat -> Buffer -> Int -> IORef (List Bits8) -> IO ()
capture Z buffer offset output = pure ()
capture (S fuel) buffer offset output = do
  byte <- getBits8 buffer offset
  modifyIORef output (\bytes => bytes ++ [byte])
  capture fuel buffer (offset + 1) output

nextWrite : Int -> List (Int, Bool) -> (Int, Bool, List (Int, Bool))
nextWrite remaining [] = (remaining, False, [])
nextWrite remaining ((count, failed) :: rest) = (count, failed, rest)

scriptWrite : IORef (List (Int, Bool)) -> IORef (List Bits8) -> Buffer -> Int -> Int -> IO BufferWrite
scriptWrite script output buffer offset remaining = do
  steps <- readIORef script
  let (count, failed, rest) = nextWrite remaining steps
  writeIORef script rest
  if count >= 0 && count <= remaining then capture (cast count) buffer offset output else pure ()
  pure (WroteBlock count failed)

newScript : List ReadStep -> List (Int, Bool) -> IO (BufferAdapters, IORef (List Bits8), IORef Nat)
newScript reads writes = do
  readScript <- newIORef reads
  writeScript <- newIORef writes
  output <- newIORef []
  flushes <- newIORef (the Nat 0)
  pure (BufferHost (scriptRead readScript) (scriptWrite writeScript output)
    (do modifyIORef flushes S; pure (Right ())), output, flushes)

readOnce : List ReadStep -> IO (Either BinaryError (Maybe Bytes))
readOnce steps = do
  (host, _, _) <- newScript steps []
  withBinaryAdapters 1 4 (bufferedBinary host) (readBytes 4)

writeOnce : List (Int, Bool) -> IO (Either BinaryError ())
writeOnce steps = do
  (host, _, _) <- newScript [] steps
  withBinaryAdapters 1 4 (bufferedBinary host) (writeBytes (fromList [0,1,2,255]))

mutatePrevious : IORef (Maybe Buffer) -> Buffer -> Int -> Int -> IO BufferRead
mutatePrevious previous buffer offset remaining = do
  saved <- readIORef previous
  case saved of
    Nothing => do
      writeIORef previous (Just buffer)
      setBits8 buffer offset 0
    Just old => do
      setBits8 old 0 255
      setBits8 buffer offset 1
  pure (ReadBlock 1 False False)

public export
runBufferChecks : IO (List (String, Bool))
runBufferChecks = do
  (host, output, flushes) <- newScript
    [Supply [0,255] False False, Supply [13] False True] [(1,False),(1,False),(1,False)]
  combined <- withBinaryAdapters 2 8 (bufferedBinary host) $ \transport => do
    result <- readBytes 5 transport
    case result of
      Right (Just bytes) => writeBytes bytes transport
      _ => pure (Left BinaryAdapterViolation)
  recorded <- readIORef output
  flushed <- readIORef flushes
  failure <- readOnce [Supply [0,1] False False, Supply [255] True False]
  eofFailure <- readOnce [Supply [0,255] True True]
  fullFailure <- readOnce [Supply [0,1,2,255] True False]
  negative <- readOnce [Claim (-1) False False]
  oversized <- readOnce [Claim 5 False False]
  stuck <- readOnce [Claim 0 False False]
  eof <- readOnce [Claim 0 False True]
  failedWrite <- writeOnce [(2,False),(1,True)]
  fullWriteFailure <- writeOnce [(4,True)]
  negativeWrite <- writeOnce [(-1,False)]
  oversizedWrite <- writeOnce [(5,False)]
  stuckWrite <- writeOnce [(0,False)]
  previous <- newIORef Nothing
  let mutable : BufferAdapters = BufferHost (mutatePrevious previous)
        (\_, _, size => pure (WroteBlock size False)) (pure (Right ()))
  copied <- withBinaryAdapters 2 2 (bufferedBinary mutable) $ \transport => do
    first <- readBytes 1 transport
    second <- readBytes 1 transport
    pure (Right (first == Right (Just (fromList [0])) && second == Right (Just (fromList [1]))))
  pure
    [("block progress shares one read/write request", combined == Right () && recorded == [0,255,13] && flushed == 1),
     ("block read failure preserves all earlier progress", failure == Left (BinaryReadFailed (fromList [0,1,255]))),
     ("block read error takes precedence over EOF", eofFailure == Left (BinaryReadFailed (fromList [0,255]))),
     ("full read count does not mask an error", fullFailure == Left (BinaryReadFailed (fromList [0,1,2,255]))),
     ("full write count does not mask an error", fullWriteFailure == Left (BinaryWriteFailed 4)),
     ("negative block read count rejected before unpack", negative == Left BinaryAdapterViolation),
     ("oversized block read count rejected before unpack", oversized == Left BinaryAdapterViolation),
     ("zero block read progress is not EOF", stuck == Left BinaryAdapterViolation),
     ("zero read with EOF flag is EOF", eof == Right Nothing),
     ("short block write failure preserves cumulative count", failedWrite == Left (BinaryWriteFailed 3)),
     ("negative block write count rejected", negativeWrite == Left BinaryAdapterViolation),
     ("oversized block write count rejected", oversizedWrite == Left BinaryAdapterViolation),
     ("zero block write progress rejected", stuckWrite == Left BinaryAdapterViolation),
     ("scratch buffer mutation cannot change immutable Bytes", copied == Right True)]
