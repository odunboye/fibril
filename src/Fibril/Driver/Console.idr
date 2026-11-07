-- Pure interpretation of checked IO descriptions into a complete stdout plan.
module Fibril.Driver.Console

import Data.List
import Fibril.Core.Context
import Fibril.Core.Term
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
  show PlanReductionLimit = "IO planning reduction budget exhausted"
  show PlanActionLimit = "IO output action count limit exceeded"
  show PlanExpectedString = "IO write argument did not normalize to a String literal"
  show PlanExpectedUnit = "IO main result did not normalize to Unit"
  show (PlanUnsupported _) = "Unsupported or neutral IO description"

record Planned where
  constructor Result
  value : Term 0
  actions : List ConsoleAction
  remaining : Nat

validate : Term 0 -> Term 0 -> Either IOPlanError ()
validate term ty = case checkRuntime checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (PlanTyping err)
  Right _ => Right ()

normal : Nat -> Term 0 -> Either IOPlanError (Term 0)
normal fuel term = case normalize fuel term of
  OutOfFuel _ => Left PlanReductionLimit
  Normal result => Right result

-- Thread one action allowance through both sides of bind; do not reset it
-- for recursive subplans. Reduction fuel remains local to each reduction call.
plan : Nat -> Nat -> Nat -> Term 0 -> Either IOPlanError Planned
plan Z fuel remaining term = Left PlanDepthLimit
plan (S depth) fuel remaining term = do
  head <- case weakHead fuel term of
    HeadLimit _ => Left PlanReductionLimit
    HeadForm head => Right head
  _ <- case inferRuntime checkingDepth typeReductionFuel Empty head of
    Left err => Left (PlanTyping err)
    Right checked => Right checked
  case head of
    IOPure value => Right (Result value [] remaining)
    WriteLine text => do
      available <- case remaining of
        Z => Left PlanActionLimit
        S available => Right available
      validate text StringType
      literal <- normal fuel text
      validate literal StringType
      case literal of
        StringValue value => Right (Result UnitValue [PrintLine value] available)
        _ => Left PlanExpectedString
    IOBind a b action next => do
      first <- plan depth fuel remaining action
      validate first.value a
      following <- plan depth fuel first.remaining (Apply next first.value)
      validate following.value b
      Right (Result following.value (first.actions ++ following.actions)
                    following.remaining)
    _ => Left (PlanUnsupported head)

||| Validate main : IO Unit, plan every effect, and validate the final Unit value.
||| Depth/head/pure-normalization budgets are not time/allocation bounds.
||| This planner performs no host IO, even when a later action fails.
public export
prepareIO : Nat -> Nat -> Term 0 -> Either IOPlanError (List ConsoleAction)
prepareIO depth fuel term = do
  if containsBinaryRequest term then Left (PlanUnsupported term) else Right ()
  validate term (IOType UnitType)
  result <- plan depth fuel consoleActionLimit term
  value <- normal fuel result.value
  validate value UnitType
  case value of
    UnitValue => Right result.actions
    _ => Left PlanExpectedUnit

||| Convert only a successfully checked and fully prepared stdout plan into a
||| host protocol program. This does not interpret source-level input or run IO.
public export
prepareConsoleProgram : Nat -> Nat -> Term 0 ->
                        Either IOPlanError (ConsoleProgram (Either String ()))
prepareConsoleProgram depth fuel term = outputProgram <$> prepareIO depth fuel term
