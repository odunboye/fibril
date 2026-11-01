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
  | FileChanged
  | BufferUnavailable
  | InvalidUTF8 UTF8Error
  | InvalidText TextError

public export
Show LoadError where
  show (FileFailure err) = "Source file IO error: " ++ show err
  show SourceTooLarge = "Source exceeds 65536-byte prototype limit"
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

readOpened : File -> IO (Either LoadError String)
readOpened file = do
  Right size <- fileSize file
    | Left err => pure (Left (FileFailure err))
  if size < 0 || size > maximumSourceBytes
     then pure (Left SourceTooLarge)
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
public export
loadSource : String -> IO (Either LoadError String)
loadSource path = do
  Right file <- openFile path Read
    | Left err => pure (Left (FileFailure err))
  result <- readOpened file
  closeFile file
  pure result
