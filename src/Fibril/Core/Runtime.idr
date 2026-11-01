-- Experimental ordinary runtime usage checking, not a soundness claim.
-- Theory: ATKEY18 sec. 2; local policy/departures: docs/runtime-checker.md.
module Fibril.Core.Runtime

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Usage
import Fibril.Core.WeakHead
import Fibril.Core.Erased

%default total

||| Failures preserve typing/exhaustion errors and identify resource mismatches.
public export
data RuntimeError
  = TypingError CheckError
  | BoundUsage Quantity Quantity
  | ContextUsage Nat Quantity Quantity
  | RuntimeTypeExpression
  | BranchUsageMismatch

public export
Show RuntimeError where
  show (TypingError err) = show err
  show (BoundUsage expected observed) =
    "Binder usage: expected " ++ show expected ++ ", observed " ++ show observed
  show (ContextUsage i expected observed) =
    "Variable " ++ show i ++ ": expected " ++ show expected ++ ", observed " ++ show observed
  show RuntimeTypeExpression = "Runtime type expressions (universe/Pi/Unit/Bool) are not supported"
  show BranchUsageMismatch = "Conditional branches use different resources"

liftTyping : Either CheckError a -> Either RuntimeError a
liftTyping (Left err) = Left (TypingError err)
liftTyping (Right value) = Right value

-- Types/annotations have already been checked through erased inference.
-- Do not validate full ambient usage for each subterm: siblings share resources.
analyze : {n : Nat} -> Nat -> Nat -> Context n -> Term n ->
          Either RuntimeError (Usage n)
analyze Z reduction context term = Left (TypingError CheckingLimit)
analyze (S depth) reduction context (Variable i) = Right (variableUsage RuntimeMode i)
analyze (S depth) reduction context (Universe _) = Left RuntimeTypeExpression
analyze (S depth) reduction context UnitType = Left RuntimeTypeExpression
analyze (S depth) reduction context UnitValue = Right zeroUsage
analyze (S depth) reduction context BoolType = Left RuntimeTypeExpression
analyze (S depth) reduction context BoolTrue = Right zeroUsage
analyze (S depth) reduction context BoolFalse = Right zeroUsage
analyze (S depth) reduction context (BoolCase condition yes no) = do
  conditionUsage <- analyze depth reduction context condition
  yesUsage <- analyze depth reduction context yes
  noUsage <- analyze depth reduction context no
  if yesUsage == noUsage
     then Right (combineUsage conditionUsage yesUsage)
     else Left BranchUsageMismatch
analyze (S depth) reduction context (Pi _ _ _) = Left RuntimeTypeExpression
analyze (S depth) reduction context (Lambda q domain body) = do
  bodyUsage <- analyze depth reduction (Extend context q domain) body
  case discharge RuntimeMode q bodyUsage of
    Right outer => Right outer
    Left err => Left (BoundUsage err.expected err.observed)
analyze (S depth) reduction context (Apply function argument) = do
  functionType <- liftTyping (inferErased depth reduction context function)
  exposed <- case weakHead reduction functionType of
    HeadForm ty => Right ty
    HeadLimit _ => Left (TypingError ReductionLimit)
  case exposed of
    Pi q domain body => do
      functionUsage <- analyze depth reduction context function
      argumentUsage <- case q of
        Erased => Right zeroUsage
        _ => analyze depth reduction context argument
      Right (combineUsage functionUsage (scaleUsage q argumentUsage))
    _ => Left (TypingError ExpectedFunction)

analyze (S depth) reduction context (UnitCase scrutinee body) = do
  scrutineeUsage <- analyze depth reduction context scrutinee
  bodyUsage <- analyze depth reduction context body
  Right (combineUsage scrutineeUsage bodyUsage)

||| A successful prototype result includes its ordinary type and observed usage.
||| It is not a proof of erasure correctness or quantitative preservation.
public export
record RuntimeResult (n : Nat) where
  constructor RuntimeChecked
  inferredType : Term n
  usage : Usage n

||| Type-check erased first, then check runtime usage and ambient permissions.
||| Erased arguments are fully type checked but not traversed as runtime values.
public export
inferRuntime : {n : Nat} -> Nat -> Nat -> Context n -> Term n ->
               Either RuntimeError (RuntimeResult n)
inferRuntime depth reduction context term = do
  ty <- liftTyping (inferErased depth reduction context term)
  observed <- analyze depth reduction context term
  case validateUsage RuntimeMode context observed of
    Right () => Right (RuntimeChecked ty observed)
    Left err => Left (ContextUsage (finToNat err.variable)
                                  err.mismatch.expected err.mismatch.observed)

||| Validate the expected type and beta comparison before runtime usage checking.
public export
checkRuntime : {n : Nat} -> Nat -> Nat -> Context n -> Term n -> Term n ->
               Either RuntimeError (RuntimeResult n)
checkRuntime depth reduction context term expected = do
  liftTyping (checkErased depth reduction context term expected)
  inferRuntime depth reduction context term
