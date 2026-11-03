-- Bounded raw-byte loading; validation does not parse or type-check programs.
module Fibril.Source.File

import Data.Buffer
import System.File
import System.File.Buffer
import Fibril.Source.UTF8
import Fibril.Source.Text

%default total

||| Small initial input cap limits accepted file bytes, not total process memory.
public export
maximumSourceBytes : Int
maximumSourceBytes = 65536

||| File errors, byte-decoding failures, and scalar-policy failures stay distinct.
public export
data LoadError
  = FileFailure FileError
  | SourceTooLarge
  | ReadLimitExceeded Int
  | InvalidReadLimit
  | FileChanged
  | BufferUnavailable
  | InvalidUTF8 UTF8Error
  | InvalidText TextError

public export
Show LoadError where
  show (FileFailure err) = "Source file IO error: " ++ show err
  show SourceTooLarge = "Source exceeds 65536-byte prototype limit"
  show (ReadLimitExceeded limit) = "File exceeds " ++ show limit ++ "-byte read limit"
  show InvalidReadLimit = "Read limit must be 0..65536 bytes"
  show FileChanged = "Source read was short or file grew while reading"
  show BufferUnavailable = "Could not allocate source buffer"
  show (InvalidUTF8 err) = show err
  show (InvalidText err) = show err

-- Call only after exact read into an allocation of at least count bytes.
bytesFrom : Buffer -> (offset : Int) -> (count : Nat) -> IO (List Bits8)
bytesFrom buffer offset Z = pure []
bytesFrom buffer offset (S count) = do
  byte <- getBits8 buffer offset
  rest <- bytesFrom buffer (offset + 1) count
  pure (byte :: rest)

readOpened : Int -> File -> IO (Either LoadError String)
readOpened maximum file = do
  Right size <- fileSize file
    | Left err => pure (Left (FileFailure err))
  if size < 0 || size > maximum
     then pure (Left (if maximum == maximumSourceBytes then SourceTooLarge else ReadLimitExceeded maximum))
     else do
       Just buffer <- newBuffer (size + 1)
         | Nothing => pure (Left BufferUnavailable)
       Right count <- readBufferData file buffer 0 size
         | Left err => pure (Left (FileFailure err))
       if count /= size
          then pure (Left FileChanged)
          else do
            Right extra <- readBufferData file buffer size 1
              | Left err => pure (Left (FileFailure err))
            if extra /= 0
               then pure (Left FileChanged)
               else do
                 bytes <- bytesFrom buffer 0 (cast size)
                 pure $ do
                   source <- case decodeUTF8 bytes of
                     Left err => Left (InvalidUTF8 err)
                     Right text => Right text
                   case validateText source of
                     Left err => Left (InvalidText err)
                     Right text => Right text

||| Read a small seekable source file as bytes, decode strictly, and validate text.
||| Close the handle on every represented success/failure after opening.
||| Reject short reads rather than retrying; this is not a streaming loader or
||| an atomic filesystem snapshot. Same-size concurrent edits are not detected.
||| Host runtime crashes/OOM/OS blocking are outside these error guarantees.
||| A smaller caller-selected cap, enforced from file size before buffer allocation.
||| The same UTF-8/control/exact-read policy applies; limits outside 0..65536 fail.
public export
loadSourceWithin : Int -> String -> IO (Either LoadError String)
loadSourceWithin maximum path =
  if maximum < 0 || maximum > maximumSourceBytes then pure (Left InvalidReadLimit) else do
    Right file <- openFile path Read
      | Left err => pure (Left (FileFailure err))
    result <- readOpened maximum file
    closeFile file
    pure result

public export
loadSource : String -> IO (Either LoadError String)
loadSource = loadSourceWithin maximumSourceBytes
