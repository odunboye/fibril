-- Pure interpretation of checked IO descriptions into a complete stdout plan.
module Fibril.Driver.Console

import Data.List
import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Effect.Console

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

validate : Term 0 -> Term 0 -> Either IOPlanError ()
validate term ty = case checkRuntime checkingDepth typeReductionFuel Empty term ty of
  Left err => Left (PlanTyping err)
  Right _ => Right ()

normal : Nat -> Term 0 -> Either IOPlanError (Term 0)
normal fuel term = case normalize fuel term of
  OutOfFuel _ => Left PlanReductionLimit
  Normal result => Right result

plan : Nat -> Nat -> Term 0 -> Either IOPlanError Planned
plan Z fuel term = Left PlanDepthLimit
plan (S depth) fuel term = do
  head <- case weakHead fuel term of
    HeadLimit _ => Left PlanReductionLimit
    HeadForm head => Right head
  _ <- case inferRuntime checkingDepth typeReductionFuel Empty head of
    Left err => Left (PlanTyping err)
    Right checked => Right checked
  case head of
    IOPure value => Right (Result value [])
    WriteLine text => do
      validate text StringType
      literal <- normal fuel text
      validate literal StringType
      case literal of
        StringValue value => Right (Result UnitValue [PrintLine value])
        _ => Left PlanExpectedString
    IOBind a b action next => do
      first <- plan depth fuel action
      validate first.value a
      following <- plan depth fuel (Apply next first.value)
      validate following.value b
      let actions = first.actions ++ following.actions
      if length actions <= 64 then Right (Result following.value actions)
         else Left PlanActionLimit
    _ => Left (PlanUnsupported head)

||| Validate main : IO Unit, plan every effect, and validate the final Unit value.
||| Depth/head/pure-normalization budgets are not time/allocation bounds.
||| This planner performs no host IO, even when a later action fails.
public export
prepareIO : Nat -> Nat -> Term 0 -> Either IOPlanError (List ConsoleAction)
prepareIO depth fuel term = do
  validate term (IOType UnitType)
  result <- plan depth fuel term
  value <- normal fuel result.value
  validate value UnitType
  case value of
    UnitValue => Right result.actions
    _ => Left PlanExpectedUnit
