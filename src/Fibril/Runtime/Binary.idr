-- Trusted C-stdio binary transport pilot. No Fibril source primitives yet.
module Fibril.Runtime.Binary

import Data.IORef
import Data.List
import Data.Maybe
import System.File
import Fibril.Data.Bytes

%default total

public export
data BinaryError
  = BinaryAdmission
  | BinaryZeroRead
  | BinaryChunkLimit
  | BinaryRequestLimit
  | BinaryByteLimit
  | BinaryReadFailed Bytes
  | BinaryWriteFailed Nat
  | BinaryFlushFailed
  | BinaryClosed
  | BinaryPoisoned
  | BinaryAdapterViolation

public export
Show BinaryError where
  show BinaryAdmission = "Binary transport admission exceeded"
  show BinaryZeroRead = "Binary reads require a positive capacity"
  show BinaryChunkLimit = "Binary chunk exceeds 65536 bytes"
  show BinaryRequestLimit = "Binary request budget exhausted"
  show BinaryByteLimit = "Binary capacity budget exhausted"
  show (BinaryReadFailed captured) = "Binary read failed after " ++ show (byteLength captured) ++ " bytes"
  show (BinaryWriteFailed accepted) = "Binary write failed after accepting " ++ show accepted ++ " bytes"
  show BinaryFlushFailed = "Binary flush failed"
  show BinaryClosed = "Binary transport is closed"
  show BinaryPoisoned = "Binary transport has a prior physical failure"
  show BinaryAdapterViolation = "Binary adapter violated its response contract"

public export
Eq BinaryError where
  BinaryAdmission == BinaryAdmission = True
  BinaryZeroRead == BinaryZeroRead = True
  BinaryChunkLimit == BinaryChunkLimit = True
  BinaryRequestLimit == BinaryRequestLimit = True
  BinaryByteLimit == BinaryByteLimit = True
  BinaryReadFailed a == BinaryReadFailed b = a == b
  BinaryWriteFailed a == BinaryWriteFailed b = a == b
  BinaryFlushFailed == BinaryFlushFailed = True
  BinaryClosed == BinaryClosed = True
  BinaryPoisoned == BinaryPoisoned = True
  BinaryAdapterViolation == BinaryAdapterViolation = True
  _ == _ = False

||| Trusted test seam. A positive read fills capacity or stops at EOF/error.
||| Nothing means EOF with no bytes; short nonempty data means EOF was reached.
public export
record BinaryAdapters where
  constructor BinaryHost
  read : Nat -> IO (Either BinaryError (Maybe Bytes))
  write : Bytes -> IO (Either BinaryError ())
  flush : IO (Either BinaryError ())

record State where
  constructor Active
  requests : Nat
  capacity : Nat
  fault : Maybe BinaryError

export
data BinaryTransport = Transport BinaryAdapters (IORef (Maybe State))

-- Account declared read capacities and write lengths, not just returned bytes.
-- EOF/short/error reads keep their reservation. Invalid sizes spend no fuel.
reserve : Nat -> BinaryTransport -> IO (Either BinaryError ())
reserve size (Transport host state) = do
  current <- readIORef state
  case current of
    Nothing => pure (Left BinaryClosed)
    Just budget => case budget.fault of
      Just _ => pure (Left BinaryPoisoned)
      Nothing => if size > 65536 then pure (Left BinaryChunkLimit)
        else case budget.requests of
          Z => pure (Left BinaryRequestLimit)
          S remaining => if size > budget.capacity then pure (Left BinaryByteLimit) else do
            writeIORef state (Just (Active remaining (budget.capacity `minus` size) Nothing))
            pure (Right ())

poison : BinaryTransport -> BinaryError -> IO (Either BinaryError a)
poison (Transport host state) err = do
  current <- readIORef state
  case current of
    Nothing => pure (Left BinaryClosed)
    Just budget => do
      let primary = fromMaybe err budget.fault
      writeIORef state (Just (Active budget.requests budget.capacity (Just primary)))
      pure (Left primary)

||| Fill a positive capacity or stop at EOF/error. Never decode or strip bytes.
||| EOF alone is Nothing; a short nonempty chunk precedes subsequent Nothing.
export
readBytes : Nat -> BinaryTransport -> IO (Either BinaryError (Maybe Bytes))
readBytes Z transport = do
  -- Closed/poisoned transports retain their original failure before validation.
  let Transport host state = transport
  current <- readIORef state
  pure $ case current of
    Nothing => Left BinaryClosed
    Just budget => maybe (Left BinaryZeroRead) (const (Left BinaryPoisoned)) budget.fault
readBytes size transport@(Transport host state) = do
  admitted <- reserve size transport
  case admitted of
    Left err => pure (Left err)
    Right () => do
      response <- host.read size
      case response of
        Left (BinaryReadFailed captured) =>
          if byteLength captured <= size then poison transport (BinaryReadFailed captured)
          else poison transport BinaryAdapterViolation
        Left _ => poison transport BinaryAdapterViolation
        Right Nothing => pure (Right Nothing)
        Right (Just bytes) => if byteLength bytes == 0 || byteLength bytes > size
          then poison transport BinaryAdapterViolation else pure (Right (Just bytes))

||| Accept the entire payload or preserve an accepted-prefix count on error.
||| Success is buffered acceptance, not durability; explicit/final flush checks.
export
writeBytes : Bytes -> BinaryTransport -> IO (Either BinaryError ())
writeBytes bytes transport@(Transport host state) = do
  admitted <- reserve (byteLength bytes) transport
  case admitted of
    Left err => pure (Left err)
    Right () => if byteLength bytes == 0 then pure (Right ()) else do
      response <- host.write bytes
      case response of
        Right () => pure (Right ())
        Left (BinaryWriteFailed count) => if count <= byteLength bytes
          then poison transport (BinaryWriteFailed count)
          else poison transport BinaryAdapterViolation
        Left _ => poison transport BinaryAdapterViolation

flushHost : BinaryTransport -> IO (Either BinaryError ())
flushHost transport@(Transport host state) = do
  response <- host.flush
  case response of
    Right () => pure (Right ())
    Left BinaryFlushFailed => poison transport BinaryFlushFailed
    Left _ => poison transport BinaryAdapterViolation

||| Explicit flush spends one request, zero byte capacity. No implicit read flush.
export
flushBytes : BinaryTransport -> IO (Either BinaryError ())
flushBytes transport = do
  admitted <- reserve 0 transport
  case admitted of
    Left err => pure (Left err)
    Right () => flushHost transport

||| Borrow streams for a sequential session. Revoke after every represented
||| callback return. Mandatory final flush on success is checked but spends no
||| request fuel. A recorded physical failure cannot be ignored by the callback.
||| Arbitrary host exceptions/cancellation are not caught. Never close streams.
export
withBinaryAdapters : Nat -> Nat -> BinaryAdapters ->
  (BinaryTransport -> IO (Either BinaryError a)) -> IO (Either BinaryError a)
withBinaryAdapters requests capacity host body =
  if requests > 100000 || capacity > 8388608 then pure (Left BinaryAdmission) else do
    state <- newIORef (Just (Active requests capacity Nothing))
    let transport = Transport host state
    result <- body transport
    current <- readIORef state
    final <- case current of
      Nothing => pure (Left BinaryClosed)
      Just budget => case budget.fault of
        Just err => pure (Left err)
        Nothing => case result of
          Left err => pure (Left err)
          Right value => do
            flushed <- flushHost transport
            pure (value <$ flushed)
    writeIORef state Nothing
    pure final

%foreign "C:fgetc,libc 6"
primGet : FilePtr -> PrimIO Int
%foreign "C:fputc,libc 6"
primPut : Int -> FilePtr -> PrimIO Int
%foreign "C:fflush,libc 6"
primFlush : FilePtr -> PrimIO Int

collect : Nat -> File -> List Bits8 -> IO (Either BinaryError (Maybe Bytes))
collect Z handle reversed = pure (Right (Just (fromList (reverse reversed))))
collect (S remaining) handle@(FHandle file) reversed = do
  failed <- fileError handle
  if failed then pure (Left (BinaryReadFailed (fromList (reverse reversed)))) else do
    byte <- primIO (primGet file)
    case byte < 0 of
      True => do
        failed <- fileError handle
        pure $ if failed then Left (BinaryReadFailed (fromList (reverse reversed)))
          else if null reversed then Right Nothing else Right (Just (fromList (reverse reversed)))
      False => collect remaining handle (cast byte :: reversed)

put : Nat -> File -> List Bits8 -> IO (Either BinaryError ())
put count handle [] = pure (Right ())
put count handle@(FHandle file) (byte :: rest) = do
  failed <- fileError handle
  if failed then pure (Left (BinaryWriteFailed count)) else do
    status <- primIO (primPut (cast byte) file)
    if status < 0 then pure (Left (BinaryWriteFailed count)) else put (S count) handle rest

||| Trusted borrowed C FILE adapters; same buffering family as text IO, never
||| raw descriptor read/write. No C-string marshalling of payload data.
export
stdioBinary : File -> File -> BinaryAdapters
stdioBinary input output@(FHandle file) = BinaryHost
  (\size => collect size input [])
  (\bytes => put 0 output (toList bytes))
  (do status <- primIO (primFlush file)
      pure (if status == 0 then Right () else Left BinaryFlushFailed))

export
withBinaryTransport : Nat -> Nat -> File -> File ->
  (BinaryTransport -> IO (Either BinaryError a)) -> IO (Either BinaryError a)
withBinaryTransport requests capacity input output =
  withBinaryAdapters requests capacity (stdioBinary input output)
