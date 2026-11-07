-- Explicit hosted binary execution; old runners never acquire this capability.
module Fibril.Driver.Binary

import Data.IORef
import Data.List
import Fibril.Core.Erased
import Fibril.Core.SharedProgram
import System.File
import Fibril.Data.Bytes
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Driver.Binary.Count
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
  | BinaryExpectedLoopStep
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
  show BinaryExpectedNat = "Binary count/capacity did not normalize to Nat"
  show BinaryExpectedBytes = "Binary write did not normalize to Bytes"
  show BinaryExpectedLoopStep = "Binary loop expects Done/Continue with a payload"
  show BinaryExpectedUnit = "Binary main did not normalize to Unit"
  show BinaryRejected = "Binary program rejected input"
  show BinaryUnsupported = "Unsupported binary IO description"
  show (BinaryTransportFailure err) = show err

validateGlobals : RuntimeGlobals -> Term 0 -> Term 0 -> Either BinaryRunError ()
validateGlobals globals term ty = case checkRuntimeGlobals globals checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (BinaryTyping err)
  Right _ => Right ()

normalGlobals : RuntimeGlobals -> Nat -> Term 0 -> Either BinaryRunError (Term 0)
normalGlobals globals fuel term = case normalizeGlobals (globalValue (erasedGlobals globals)) fuel term of
  OutOfFuel _ => Left BinaryReductionLimit
  Normal value => Right value

public export
prepareBinaryGlobals : RuntimeGlobals -> Term 0 -> Either BinaryRunError ()
prepareBinaryGlobals globals term = do
  declarations <- case reachableGlobals globals term of
    Left _ => Left BinaryEntryAdmission
    Right declarations => Right declarations
  let syntax : List (Term 0) = term :: concatMap (\(_, _, ty, body) => [ty, body]) declarations
  if any (containsNonBinaryIO . maskGlobalRefs) syntax || sharedProgramNodes term declarations > 8192 || sharedProgramPayload term declarations > payloadLimit
    then Left BinaryEntryAdmission else Right ()
  validateGlobals globals term (IOType UnitType)

responseValue : Maybe Bytes -> Term 0
responseValue Nothing = VariantValue byteReadResultType 0 Nothing
responseValue (Just bytes) = VariantValue byteReadResultType 1 (Just (BytesValue bytes))

liftTransport : Either BinaryError a -> Either BinaryRunError a
liftTransport (Left err) = Left (BinaryTransportFailure err)
liftTransport (Right value) = Right value

-- prepareBinary checks the original compact syntax. Re-inferring a decoded
-- unary count here would impose checkingDepth on an execution representation.
checkDescriptionGlobals : RuntimeGlobals -> Term 0 -> Either BinaryRunError ()
checkDescriptionGlobals globals (IterateBinary _ _ _ _ _) = Right ()
checkDescriptionGlobals globals head = case inferRuntimeGlobals globals checkingDepth typeReductionFuel Empty head of
  Left err => Left (BinaryTyping err)
  Right _ => Right ()

mutual
  covering
  executeGlobals : RuntimeGlobals -> Nat -> Nat -> BinaryTransport -> Term 0 -> IO (Either BinaryRunError (Term 0))
  executeGlobals globals Z fuel transport term = pure (Left BinaryDepthLimit)
  executeGlobals globals (S depth) fuel transport term = case weakHeadGlobals (globalValue (erasedGlobals globals)) fuel term of
    HeadLimit _ => pure (Left BinaryReductionLimit)
    HeadForm head => case checkDescriptionGlobals globals head of
      Left err => pure (Left err)
      Right () => case head of
        IterateBinary stateType resultType count step initial => case decodeBinaryCountGlobals (globalValue (erasedGlobals globals)) fuel count of
          Left CountReductionLimit => pure (Left BinaryReductionLimit)
          Left CountExpectedNat => pure (Left BinaryExpectedNat)
          Right limit => iterateGlobals globals depth fuel transport stateType resultType limit step initial
        IOPure value => pure (Right value)
        ReadBytes capacity => case normalGlobals globals fuel capacity >>= maybe (Left BinaryExpectedNat) Right . canonicalNatural of
          Left err => pure (Left err)
          Right size => do
            result <- readBytes size transport
            pure $ do
              bytes <- liftTransport result
              let value = responseValue bytes
              validateGlobals globals value byteReadResultType
              Right value
        WriteBytes dataTerm => case normalGlobals globals fuel dataTerm of
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
          first <- executeGlobals globals depth fuel transport action
          case first >>= (\value => value <$ validateGlobals globals value a) of
            Left err => pure (Left err)
            Right value => do
              following <- executeGlobals globals depth fuel transport (Apply next value)
              pure (following >>= (\result => result <$ validateGlobals globals result b))
        _ => pure (Left BinaryUnsupported)

  covering
  iterateGlobals : RuntimeGlobals -> Nat -> Nat -> BinaryTransport -> Term 0 -> Term 0 -> Nat -> Term 0 -> Term 0 ->
            IO (Either BinaryRunError (Term 0))
  iterateGlobals globals depth fuel transport stateType resultType Z step state =
    pure (Right (VariantValue (loopVariantType stateType resultType) 1 (Just state)))
  iterateGlobals globals Z fuel transport stateType resultType (S limit) step state = pure (Left BinaryDepthLimit)
  iterateGlobals globals (S depth) fuel transport stateType resultType (S limit) step state =
    case weakHeadGlobals (globalValue (erasedGlobals globals)) fuel state of
      HeadLimit _ => pure (Left BinaryReductionLimit)
      HeadForm ready => do
        response <- executeGlobals globals depth fuel transport (Apply step ready)
        case response of
          Left err => pure (Left err)
          Right value => case weakHeadGlobals (globalValue (erasedGlobals globals)) fuel value of
            HeadLimit _ => pure (Left BinaryReductionLimit)
            HeadForm (VariantValue _ 0 (Just result)) =>
              pure (Right (VariantValue (loopVariantType stateType resultType) 0 (Just result)))
            HeadForm (VariantValue _ 1 (Just next)) =>
              iterateGlobals globals depth fuel transport stateType resultType limit step next
            _ => pure (Left BinaryExpectedLoopStep)

||| The optional driver error carries non-transport failure across the trusted
||| session callback without reporting success (which would trigger final flush).
||| Physical errors remain BinaryError values, including consumed read prefixes.
public export
covering
runBinaryTermWithGlobals : RuntimeGlobals -> Nat -> Nat -> Nat -> Nat -> BinaryAdapters -> Term 0 -> IO (Either BinaryRunError ())
runBinaryTermWithGlobals globals depth fuel requests capacity host term =
  if depth > 8192 || fuel > 100000 then pure (Left BinaryEntryAdmission) else
  case prepareBinaryGlobals globals term of
    Left err => pure (Left err)
    Right () => do
      driverFailure <- newIORef Nothing
      result <- withBinaryAdapters requests capacity host $ \transport => do
        interpreted <- executeGlobals globals depth fuel transport term
        let completed = do
              value <- interpreted
              value <- normalGlobals globals fuel value
              validateGlobals globals value UnitType
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
prepareBinary : Term 0 -> Either BinaryRunError ()
prepareBinary = prepareBinaryGlobals emptyRuntimeGlobals


public export
covering
runBinaryTermWith : Nat -> Nat -> Nat -> Nat -> BinaryAdapters -> Term 0 -> IO (Either BinaryRunError ())
runBinaryTermWith = runBinaryTermWithGlobals emptyRuntimeGlobals

public export
covering
runBinaryProject : String -> String -> IO (Either String ())
runBinaryProject root entry = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => do
      result <- runBinaryTermWithGlobals project.globals 4096 4096 4096 8388608 (stdioBinary stdin stdout) project.term
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
