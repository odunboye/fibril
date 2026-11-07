-- Pure interpretation of checked IO descriptions into a complete stdout plan.
module Fibril.Driver.Console

import Data.List
import Fibril.Core.Erased
import Fibril.Core.SharedProgram
import Fibril.Core.Context
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Evaluation
import Fibril.Core.EffectAdmission
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Effect.Console
import Fibril.Effect.ConsoleProgram

import Fibril.Driver.Limits

%default total

public export
data IOPlanError
  = PlanTyping RuntimeError
  | PlanDepthLimit
  | PlanReductionLimit
  | PlanActionLimit
  | PlanExpectedString
  | PlanExpectedUnit
  | PlanUnsupported (Term 0)

public export
Show IOPlanError where
  show (PlanTyping err) = "IO planning check: " ++ show err
  show PlanDepthLimit = "IO planning depth budget exhausted"
  show PlanReductionLimit = "IO planning reduction budget exhausted; raise it with run --fuel N (0..4096)"
  show PlanActionLimit = "IO output action count limit exceeded"
  show PlanExpectedString = "IO write argument did not normalize to a String literal"
  show PlanExpectedUnit = "IO main result did not normalize to Unit"
  show (PlanUnsupported _) = "Unsupported or neutral IO description"

record Planned where
  constructor Result
  value : Term 0
  actions : List ConsoleAction
  remaining : Nat

validateGlobals : RuntimeGlobals -> Term 0 -> Term 0 -> Either IOPlanError ()
validateGlobals globals term ty = case checkRuntimeGlobals globals checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (PlanTyping err)
  Right _ => Right ()

normalGlobals : RuntimeGlobals -> Nat -> Term 0 -> Either IOPlanError (Term 0)
normalGlobals globals fuel term = case normalizeRunGlobals (globalValue (erasedGlobals globals)) fuel term of
  OutOfFuel _ => Left PlanReductionLimit
  Normal result => Right result

-- Thread one action allowance through both sides of bind; do not reset it
-- for recursive subplans. Reduction fuel remains local to each reduction call.
planGlobals : RuntimeGlobals -> Nat -> Nat -> Nat -> Term 0 -> Either IOPlanError Planned
planGlobals globals Z fuel remaining term = Left PlanDepthLimit
planGlobals globals (S depth) fuel remaining term = do
  head <- case weakHeadRunGlobals (globalValue (erasedGlobals globals)) fuel term of
    HeadLimit _ => Left PlanReductionLimit
    HeadForm head => Right head
  _ <- case inferRuntimeGlobals globals checkingDepth typeReductionFuel Empty head of
    Left err => Left (PlanTyping err)
    Right checked => Right checked
  case head of
    IOPure value => Right (Result value [] remaining)
    WriteLine text => do
      available <- case remaining of
        Z => Left PlanActionLimit
        S available => Right available
      validateGlobals globals text StringType
      literal <- normalGlobals globals fuel text
      validateGlobals globals literal StringType
      case literal of
        StringValue value => Right (Result UnitValue [PrintLine value] available)
        _ => Left PlanExpectedString
    IOBind a b action next => do
      first <- planGlobals globals depth fuel remaining action
      validateGlobals globals first.value a
      following <- planGlobals globals depth fuel first.remaining (Apply next first.value)
      validateGlobals globals following.value b
      Right (Result following.value (first.actions ++ following.actions)
                    following.remaining)
    _ => Left (PlanUnsupported head)

||| Validate main : IO Unit, plan every effect, and validate the final Unit value.
||| Depth/head/pure-normalization budgets are not time/allocation bounds.
||| This planner performs no host IO, even when a later action fails.
public export
prepareIOGlobals : RuntimeGlobals -> Nat -> Nat -> Term 0 -> Either IOPlanError (List ConsoleAction)
prepareIOGlobals globals depth fuel term = do
  declarations <- case reachableGlobals globals term of
    Left _ => Left (PlanUnsupported term)
    Right declarations => Right declarations
  let syntax : List (Term 0) = term :: concatMap (\(_, _, ty, body) => [ty, body]) declarations
  if any (containsBinaryRequest . maskGlobalRefs) syntax then Left (PlanUnsupported term) else Right ()
  validateGlobals globals term (IOType UnitType)
  result <- planGlobals globals depth fuel consoleActionLimit term
  value <- normalGlobals globals fuel result.value
  validateGlobals globals value UnitType
  case value of
    UnitValue => Right result.actions
    _ => Left PlanExpectedUnit

||| Convert only a successfully checked and fully prepared stdout plan into a
||| host protocol program. This does not interpret source-level input or run IO.
public export
prepareConsoleProgramGlobals : RuntimeGlobals -> Nat -> Nat -> Term 0 ->
                        Either IOPlanError (ConsoleProgram (Either String ()))
prepareConsoleProgramGlobals globals depth fuel term = outputProgram <$> prepareIOGlobals globals depth fuel term

public export
prepareIO : Nat -> Nat -> Term 0 -> Either IOPlanError (List ConsoleAction)
prepareIO = prepareIOGlobals emptyRuntimeGlobals

public export
prepareConsoleProgram : Nat -> Nat -> Term 0 ->
                        Either IOPlanError (ConsoleProgram (Either String ()))
prepareConsoleProgram = prepareConsoleProgramGlobals emptyRuntimeGlobals
