-- Trusted hosted execution of checked scoped descriptions. No source file API.
module Fibril.Driver.Resource

import Data.IORef
import System.File
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Size
import Fibril.Core.ResourceAdmission
import Fibril.Core.Limits
import Fibril.Elaboration.Expression.Payload
import Fibril.Driver.Interactive
import Fibril.Runtime.Console
import Fibril.Runtime.ConsoleInput
import Fibril.Runtime.ScopedInput
import Fibril.Effect.Console

%default total

public export
data ResourceError
  = ResourceTyping RuntimeError
  | ResourceAdmission
  | ResourceDepthLimit
  | ResourceReductionLimit
  | ResourceRequestLimit
  | ResourceUnsupported
  | ResourceExpectedString
  | ResourceExpectedUnit
  | ResourceOwnershipReturn
  | ResourceWriteFailure String
  | ResourceCleanupFailure ResourceError ScopedInputError

public export
Show ResourceError where
  show (ResourceTyping err) = "Resource check: " ++ show err
  show ResourceAdmission = "Resource entry rejects runtime references or exceeds admission limits"
  show ResourceDepthLimit = "Resource description depth exhausted"
  show ResourceReductionLimit = "Resource reduction budget exhausted"
  show ResourceRequestLimit = "Resource request budget exhausted"
  show ResourceUnsupported = "Unsupported resource IO description"
  show ResourceExpectedString = "Resource path/write operand did not normalize to String"
  show ResourceExpectedUnit = "Resource main did not normalize to Unit"
  show ResourceOwnershipReturn = "Scope did not return its matching ownership pair"
  show (ResourceWriteFailure err) = "Resource output failed: " ++ err
  show (ResourceCleanupFailure primary cleanup) = show primary ++ "; cleanup: " ++ show cleanup

||| Adapters and observer are trusted host callbacks. The observer permits lease
||| lifetime tests without exposing a raw File; production uses a no-op observer.
public export
record ResourceAdapters where
  constructor ResourceHost
  writeOutput : String -> IO (Either String ())
  readInput : IO (Either String (Maybe String))
  flushOutput : IO (Either String ())
  observeLease : Nat -> ScopedInput -> IO ()

public export
record ResourceExecution where
  constructor ExecutedResources
  outcome : Either ResourceError ()
  cleanupFailures : List ScopedInputError
  regionsCreated : Nat

validate : Term 0 -> Term 0 -> Either ResourceError ()
validate term ty = case checkRuntime checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (ResourceTyping err)
  Right _ => Right ()

normal : Nat -> Term 0 -> Either ResourceError (Term 0)
normal fuel term = case normalize fuel term of
  OutOfFuel _ => Left ResourceReductionLimit
  Normal value => Right value

stringValue : Nat -> Term 0 -> Either ResourceError String
stringValue fuel term = do
  value <- normal fuel term
  case value of
    StringValue text => Right text
    _ => Left ResourceExpectedString

consumeRequest : IORef Nat -> IO (Either ResourceError ())
consumeRequest remaining = do
  available <- readIORef remaining
  case available of
    Z => pure (Left ResourceRequestLimit)
    S rest => writeIORef remaining rest >> pure (Right ())

returnedOwnership : Nat -> Nat -> Term 0 -> Term 0 -> Either ResourceError (Term 0)
returnedOwnership fuel identity result value = do
  exposed <- normal fuel value
  validate exposed (Sigma Linear Linear (FileHandleType (runtimeFileRegion identity)) (weaken result))
  case exposed of
    PairValue _ (FileHandleValue returned) payload =>
      if identity == returned then validate payload result >> Right payload
      else Left ResourceOwnershipReturn
    _ => Left ResourceOwnershipReturn

-- Every recursive description interpretation decreases depth. Request fuel is
-- shared through the entire run, but mandatory cleanup never consumes it.
execute : Nat -> Nat -> IORef Nat -> IORef Nat -> InputSession -> ResourceAdapters ->
          Term 0 -> IO (Either ResourceError (Term 0))
execute Z fuel requests next session host term = pure (Left ResourceDepthLimit)
execute (S depth) fuel requests next session host term =
  case weakHead fuel term of
    HeadLimit _ => pure (Left ResourceReductionLimit)
    HeadForm head => case inferRuntime checkingDepth typeReductionFuel Empty head of
      Left err => pure (Left (ResourceTyping err))
      Right _ => case head of
        IOPure value => pure (Right value)
        WriteLine text => case stringValue fuel text of
          Left err => pure (Left err)
          Right value => do
            allowed <- consumeRequest requests
            case allowed of
              Left err => pure (Left err)
              Right () => do
                written <- host.writeOutput value
                pure $ case written of
                  Left err => Left (ResourceWriteFailure err)
                  Right () => Right UnitValue
        ReadLine => do
          allowed <- consumeRequest requests
          case allowed of
            Left err => pure (Left err)
            Right () => do
              response <- host.readInput
              pure (Right (readResponseValue response))
        IOBind a b action continuation => do
          first <- execute depth fuel requests next session host action
          case first of
            Left err => pure (Left err)
            Right value => case validate value a of
              Left err => pure (Left err)
              Right () => do
                following <- execute depth fuel requests next session host (Apply continuation value)
                pure $ do
                  result <- following
                  validate result b
                  Right result
        WithInputFile result path body => case stringValue fuel path of
          Left err => pure (Left err)
          Right filename => do
            allowed <- consumeRequest requests
            case allowed of
              Left err => pure (Left err)
              Right () => do
                opened <- openSessionInput session filename
                case opened of
                  Left err => pure (Right (VariantValue (fileScopeResultType result) 0
                                    (Just (StringValue (show err)))))
                  Right lease => do
                    identity <- readIORef next
                    writeIORef next (S identity)
                    host.observeLease identity lease
                    computed <- execute depth fuel requests next session host
                      (Apply (Apply body (runtimeFileRegion identity)) (FileHandleValue identity))
                    let returned = computed >>= returnedOwnership fuel identity result
                    closed <- closeScopedInput lease
                    pure $ case (returned, closed) of
                      (Left primary, Left cleanup) => Left (ResourceCleanupFailure primary cleanup)
                      (Left primary, Right ()) => Left primary
                      (Right value, Right ()) => Right (VariantValue (fileScopeResultType result) 1 (Just value))
                      (Right value, Left cleanup) => Right (VariantValue (fileScopeResultType result) 2
                        (Just (PairValue (Sigma Linear Linear result StringType) value (StringValue (show cleanup)))))
        _ => pure (Left ResourceUnsupported)

||| Caller syntax cannot contain internal runtime handles, even in erased fields.
||| Scope IDs are fresh within this session only; no raw File appears in a term.
||| Session cleanup preserves failures independently of the primary run outcome.
public export
runResourceTermWith : Nat -> Nat -> Nat -> ResourceAdapters -> Term 0 -> IO ResourceExecution
runResourceTermWith depth fuel requestLimit host term =
  if containsFileReference term || coreNodes term > 8192 || payloadSize term > payloadLimit
    then pure (ExecutedResources (Left ResourceAdmission) [] 0)
    else case validate term (IOType UnitType) of
      Left err => pure (ExecutedResources (Left err) [] 0)
      Right () => do
        requests <- newIORef requestLimit
        next <- newIORef 0
        (result, failures) <- withInputSession (\session => do
          interpreted <- execute depth fuel requests next session host term
          let normalized : Either ResourceError (Term 0)
              normalized = interpreted >>= normal fuel
          case normalized of
            Left err => pure (Left err)
            Right value => case validate value UnitType of
              Left err => pure (Left err)
              Right () => case value of
                UnitValue => do
                  flushed <- host.flushOutput
                  pure $ case flushed of
                    Left err => Left (ResourceWriteFailure err)
                    Right () => Right ()
                _ => pure (Left ResourceExpectedUnit))
        created <- readIORef next
        pure (ExecutedResources result failures created)

||| Explicit host-only entry. Source/native resource operations remain disabled.
public export
covering
runResourceTerm : Term 0 -> IO ResourceExecution
runResourceTerm = runResourceTermWith 128 128 64
  (ResourceHost (\text => executeConsole (PrintLine text))
    (readAfterFlush flushStdout (readConsoleLine 8192 stdin)) flushStdout (\_, _ => pure ()))
