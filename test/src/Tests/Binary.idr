module Tests.Binary

import Data.IORef
import Fibril.Data.Bytes
import Fibril.Runtime.Binary

%default total

public export
checks : List (String, Bool)
checks =
  [("empty bytes have zero length", byteLength empty == 0),
   ("bytes preserve NUL and high octets", toList (fromList [0, 255, 128, 13, 10]) == [0, 255, 128, 13, 10]),
   ("byte lengths are not UTF-8 scalar lengths", byteLength (fromList [240, 159, 140, 141]) == 4),
   ("byte append is exact", append (fromList [0, 255]) (fromList [1]) == fromList [0, 255, 1]),
   ("byte slice is bounded", slice 1 99 (fromList [0, 255, 1]) == fromList [255, 1]),
   ("out-of-range byte slice is empty", slice 99 1 (fromList [0]) == empty)]

eofRead : Nat -> IO (Either BinaryError (Maybe Bytes))
eofRead size = pure (Right Nothing)

countedEOF : IORef Nat -> Nat -> IO (Either BinaryError (Maybe Bytes))
countedEOF counter size = do
  modifyIORef counter S
  pure (Right Nothing)

public export
runChecks : IO (List (String, Bool))
runChecks = do
  reads <- newIORef 0
  writes <- newIORef 0
  flushes <- newIORef 0
  let host : BinaryAdapters = BinaryHost
        (\n => do modifyIORef reads S; pure (Right (Just (fromList [255]))))
        (\bytes => do modifyIORef writes S; pure (Right ()))
        (do modifyIORef flushes S; pure (Right ()))
  recovered <- withBinaryAdapters 2 2 host $ \transport => do
    zero <- readBytes 0 transport
    large <- readBytes 65537 transport
    quota <- readBytes 3 transport
    one <- readBytes 1 transport
    written <- writeBytes (fromList [0]) transport
    pure (Right (zero == Left BinaryZeroRead && large == Left BinaryChunkLimit &&
      quota == Left BinaryByteLimit && one == Right (Just (fromList [255])) && written == Right ()))
  readCount <- readIORef reads
  writeCount <- readIORef writes
  flushCount <- readIORef flushes
  exhausted <- withBinaryAdapters 0 0 host (\transport => readBytes 1 transport)
  noRead <- readIORef reads
  noBody <- newIORef True
  refused <- withBinaryAdapters 100001 0 host (\transport => do writeIORef noBody False; pure (Right ()))
  untouched <- readIORef noBody
  refusedCapacity <- withBinaryAdapters 1 8388609 host (\transport => do writeIORef noBody False; pure (Right ()))
  untouchedCapacity <- readIORef noBody
  emptyWrites <- newIORef (the Nat 0)
  let emptyHost : BinaryAdapters = BinaryHost eofRead
        (\bytes => do modifyIORef emptyWrites S; pure (Right ())) (pure (Right ()))
  emptyWrite <- withBinaryAdapters 1 0 emptyHost (writeBytes empty)
  emptyCount <- readIORef emptyWrites
  eofReads <- newIORef (the Nat 0)
  let eofHost : BinaryAdapters = BinaryHost (countedEOF eofReads)
        (\_ => pure (Right ())) (pure (Right ()))
  chargedEOF <- withBinaryAdapters 2 2 eofHost $ \transport => do
    first <- readBytes 2 transport
    second <- readBytes 1 transport
    pure (Right (first == Right Nothing && second == Left BinaryByteLimit))
  eofCount <- readIORef eofReads
  let failingRead : BinaryAdapters = BinaryHost (\_ => pure (Left (BinaryReadFailed (fromList [0, 255]))))
        (\_ => do modifyIORef writes S; pure (Right ()))
        (do modifyIORef flushes S; pure (Right ()))
  readPoison <- newIORef False
  failedRead <- withBinaryAdapters 4 10 failingRead $ \transport => do
    first <- readBytes 3 transport
    next <- readBytes 1 transport
    output <- writeBytes (fromList [1]) transport
    writeIORef readPoison (first == Left (BinaryReadFailed (fromList [0, 255])) &&
      next == Left BinaryPoisoned && output == Left BinaryPoisoned)
    pure (Right ()) -- First physical failure must survive deliberate handling.
  poisoned <- readIORef readPoison
  afterWrites <- readIORef writes
  afterFlushes <- readIORef flushes
  let failingWrite : BinaryAdapters = BinaryHost eofRead
        (\_ => pure (Left (BinaryWriteFailed 2))) (pure (Right ()))
  failedWrite <- withBinaryAdapters 1 3 failingWrite $ \transport => do
    _ <- writeBytes (fromList [0, 1, 255]) transport
    pure (Right ())
  let badRead : BinaryAdapters = BinaryHost (\_ => pure (Right (Just empty)))
        (\_ => pure (Right ())) (pure (Right ()))
  violated <- withBinaryAdapters 1 1 badRead (readBytes 1)
  let badWrite : BinaryAdapters = BinaryHost eofRead
        (\_ => pure (Left (BinaryWriteFailed 99))) (pure (Right ()))
  violatedWrite <- withBinaryAdapters 1 1 badWrite (writeBytes (fromList [1]))
  let failedFlushHost : BinaryAdapters = BinaryHost eofRead
        (\_ => pure (Right ())) (pure (Left BinaryFlushFailed))
  finalFlush <- withBinaryAdapters 0 0 failedFlushHost (\_ => pure (Right ()))
  explicitFlush <- withBinaryAdapters 0 0 host flushBytes
  escaped <- withBinaryAdapters 0 0 host (\transport => pure (Right transport))
  closed <- case escaped of
    Left _ => pure False
    Right transport => do
      first <- readBytes 0 transport
      second <- writeBytes empty transport
      third <- flushBytes transport
      pure (first == Left BinaryClosed && second == Left BinaryClosed && third == Left BinaryClosed)
  pure
    [("invalid sizes do not spend requests or touch IO", recovered == Right True && readCount == 1 && writeCount == 1),
     ("mandatory final flush spends no request", flushCount == 1),
     ("request exhaustion prevents reads", exhausted == Left BinaryRequestLimit && noRead == readCount),
     ("admission rejection skips callback", refused == Left BinaryAdmission && untouched &&
       refusedCapacity == Left BinaryAdmission && untouchedCapacity),
     ("empty writes spend a request without invoking payload IO", emptyWrite == Right () && emptyCount == 0),
     ("EOF reserves requested capacity", chargedEOF == Right True && eofCount == 1),
     ("read failures preserve consumed binary prefix", poisoned && failedRead == Left (BinaryReadFailed (fromList [0, 255]))),
     ("poison prevents subsequent IO and implicit flush", afterWrites == writeCount && afterFlushes == flushCount),
     ("write failures preserve accepted count", failedWrite == Left (BinaryWriteFailed 2)),
     ("empty successful positive read is invalid", violated == Left BinaryAdapterViolation),
     ("impossible accepted count is invalid", violatedWrite == Left BinaryAdapterViolation),
     ("mandatory flush failures are represented", finalFlush == Left BinaryFlushFailed),
     ("explicit flush needs request fuel", explicitFlush == Left BinaryRequestLimit),
     ("escaped transports are revoked", closed)]
