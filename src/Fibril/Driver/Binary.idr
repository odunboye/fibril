-- Explicit hosted binary execution; old runners never acquire this capability.
module Fibril.Driver.Binary

import Data.IORef
import System.File
import Fibril.Data.Bytes
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Limits
import Fibril.Core.Size
import Fibril.Core.EffectAdmission
import Fibril.Elaboration.Expression.Payload
import Fibril.Runtime.Binary
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default total

public export
data BinaryRunError
  = BinaryTyping RuntimeError
  | BinaryEntryAdmission
  | BinaryDepthLimit
  | BinaryReductionLimit
  | BinaryExpectedNat
  | BinaryExpectedBytes
  | BinaryExpectedUnit
  | BinaryRejected
  | BinaryUnsupported
  | BinaryTransportFailure BinaryError

public export
Show BinaryRunError where
  show (BinaryTyping err) = "Binary check: " ++ show err
  show BinaryEntryAdmission = "Binary entry rejects non-binary IO/references or exceeds admission limits"
  show BinaryDepthLimit = "Binary description depth exhausted"
  show BinaryReductionLimit = "Binary reduction budget exhausted"
  show BinaryExpectedNat = "Binary read capacity did not normalize to Nat"
  show BinaryExpectedBytes = "Binary write did not normalize to Bytes"
  show BinaryExpectedUnit = "Binary main did not normalize to Unit"
  show BinaryRejected = "Binary program rejected input"
  show BinaryUnsupported = "Unsupported binary IO description"
  show (BinaryTransportFailure err) = show err

validate : Term 0 -> Term 0 -> Either BinaryRunError ()
validate term ty = case checkRuntime checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (BinaryTyping err)
  Right _ => Right ()

normal : Nat -> Term 0 -> Either BinaryRunError (Term 0)
normal fuel term = case normalize fuel term of
  OutOfFuel _ => Left BinaryReductionLimit
  Normal value => Right value

public export
prepareBinary : Term 0 -> Either BinaryRunError ()
prepareBinary term = do
  if containsNonBinaryIO term || coreNodes term > 8192 || payloadSize term > payloadLimit
    then Left BinaryEntryAdmission else Right ()
  validate term (IOType UnitType)

responseValue : Maybe Bytes -> Term 0
responseValue Nothing = VariantValue byteReadResultType 0 Nothing
responseValue (Just bytes) = VariantValue byteReadResultType 1 (Just (BytesValue bytes))

liftTransport : Either BinaryError a -> Either BinaryRunError a
liftTransport (Left err) = Left (BinaryTransportFailure err)
liftTransport (Right value) = Right value

covering
execute : Nat -> Nat -> BinaryTransport -> Term 0 -> IO (Either BinaryRunError (Term 0))
execute Z fuel transport term = pure (Left BinaryDepthLimit)
execute (S depth) fuel transport term = case weakHead fuel term of
  HeadLimit _ => pure (Left BinaryReductionLimit)
  HeadForm head => case inferRuntime checkingDepth typeReductionFuel Empty head of
    Left err => pure (Left (BinaryTyping err))
    Right _ => case head of
      IOPure value => pure (Right value)
      ReadBytes capacity => case normal fuel capacity >>= maybe (Left BinaryExpectedNat) Right . canonicalNatural of
        Left err => pure (Left err)
        Right size => do
          result <- readBytes size transport
          pure $ do
            bytes <- liftTransport result
            let value = responseValue bytes
            validate value byteReadResultType
            Right value
      WriteBytes dataTerm => case normal fuel dataTerm of
        Left err => pure (Left err)
        Right (BytesValue bytes) => do
          result <- writeBytes bytes transport
          pure (UnitValue <$ liftTransport result)
        Right _ => pure (Left BinaryExpectedBytes)
      RejectBytes => pure (Left BinaryRejected)
      FlushBytes => do
        result <- flushBytes transport
        pure (UnitValue <$ liftTransport result)
      IOBind a b action next => do
        first <- execute depth fuel transport action
        case first >>= (\value => value <$ validate value a) of
          Left err => pure (Left err)
          Right value => do
            following <- execute depth fuel transport (Apply next value)
            pure (following >>= (\result => result <$ validate result b))
      _ => pure (Left BinaryUnsupported)

||| The optional driver error carries non-transport failure across the trusted
||| session callback without reporting success (which would trigger final flush).
||| Physical errors remain BinaryError values, including consumed read prefixes.
public export
covering
runBinaryTermWith : Nat -> Nat -> Nat -> Nat -> BinaryAdapters -> Term 0 -> IO (Either BinaryRunError ())
runBinaryTermWith depth fuel requests capacity host term =
  if depth > 8192 || fuel > 100000 then pure (Left BinaryEntryAdmission) else
  case prepareBinary term of
    Left err => pure (Left err)
    Right () => do
      driverFailure <- newIORef Nothing
      result <- withBinaryAdapters requests capacity host $ \transport => do
        interpreted <- execute depth fuel transport term
        let completed = do
              value <- interpreted
              value <- normal fuel value
              validate value UnitType
              case value of
                UnitValue => Right ()
                _ => Left BinaryExpectedUnit
        case completed of
          Right () => pure (Right ())
          Left (BinaryTransportFailure err) => pure (Left err)
          Left err => do
            writeIORef driverFailure (Just err)
            pure (Left BinaryAdapterViolation)
      other <- readIORef driverFailure
      pure $ case other of
        Just err => Left err
        Nothing => case result of
          Left err => Left (BinaryTransportFailure err)
          Right () => Right ()

public export
covering
runBinaryProject : String -> String -> IO (Either String ())
runBinaryProject root entry = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => do
      result <- runBinaryTermWith 4096 4096 4096 8388608 (stdioBinary stdin stdout) project.term
      pure $ case result of
        Left err => Left (show err)
        Right () => Right ()

public export
covering
runBinaryFile : String -> IO (Either String ())
runBinaryFile path = do
  loaded <- loadSource path
  case loaded of
    Left err => pure (Left (renderFileError path (show err)))
    Right source => case resolveSource source of
      Left err => pure (Left (renderDriverError path source (FrontendFailure err)))
      Right term => do
        result <- runBinaryTermWith 4096 4096 4096 8388608 (stdioBinary stdin stdout) term
        pure $ case result of
          Left err => Left (renderFileError path (show err))
          Right () => Right ()
