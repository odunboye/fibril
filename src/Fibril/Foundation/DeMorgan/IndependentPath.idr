-- Experimental closed-path judgment, separate from the Fibril core checker.
module Fibril.Foundation.DeMorgan.IndependentPath

import Data.Fin
import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.ClosedPath
import Fibril.Foundation.DeMorgan.ClosedCorePath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| A checked closed `Path Bool left right` formation, with opaque endpoints.
||| This is an experimental judgment, not a Fibril core type.
export
data CheckedBoolPathType : Type where
  MkCheckedBoolPathType : Term 0 -> Term 0 -> CheckedBoolPathType

||| Opaque evidence of acceptance by the restricted experimental path checker.
||| It is not a Fibril core term or evidence of resource-safe runtime use.
export
data CheckedClosedPath : Type where
  MkCheckedClosedPath : CorePathExpr 0 -> Term 0 -> Term 0 -> CheckedClosedPath

||| Opaque evidence that a closed core Boolean passed this restricted checker.
||| It is not a runtime resource judgment.
export
data CheckedClosedBool : Type where
  MkCheckedClosedBool : Term 0 -> CheckedClosedBool

||| Failure cannot represent successful checking. Exhaustion is inconclusive,
||| while rejection covers mismatched or unsupported inputs.
public export
data ClosedPathFailure = ClosedPathRejected | ClosedPathExhausted

||| Form `Path Bool left right` only when both closed endpoints are independently
||| accepted as Boolean terms in the restricted fragment. Different endpoints are
||| permitted: formation does not assert that a path between them exists.
export
formClosedBoolPath : Nat -> Nat -> Nat -> Term 0 -> Term 0 ->
                     Either ClosedPathFailure CheckedBoolPathType
formClosedBoolPath depth reduction fuel left right =
  case checkClosedCorePath depth reduction fuel left left left of
    Rejected => Left ClosedPathRejected
    Exhausted => Left ClosedPathExhausted
    Accepted => case checkClosedCorePath depth reduction fuel right right right of
      Rejected => Left ClosedPathRejected
      Exhausted => Left ClosedPathExhausted
      Accepted => Right (MkCheckedBoolPathType left right)

||| Check a path against an already-formed type. The checker repeats all
||| relevant checks under the caller's budgets, rather than trusting annotations.
export
checkPathAgainstType : Nat -> Nat -> Nat -> CorePathExpr 0 -> CheckedBoolPathType ->
                       Either ClosedPathFailure CheckedClosedPath
checkPathAgainstType depth reduction fuel path (MkCheckedBoolPathType left right) =
  case checkCorePathExpr depth reduction fuel path left right of
    Accepted => Right (MkCheckedClosedPath path left right)
    Rejected => Left ClosedPathRejected
    Exhausted => Left ClosedPathExhausted

||| Reject unsupported inputs and propagate exhausted checks without producing
||| a witness. The witness records exactly the checked expression and endpoints.
export
checkClosedPath : Nat -> Nat -> Nat -> CorePathExpr 0 -> Term 0 -> Term 0 ->
                  Either ClosedPathFailure CheckedClosedPath
checkClosedPath depth reduction fuel path left right =
  case checkCorePathExpr depth reduction fuel path left right of
    Accepted => Right (MkCheckedClosedPath path left right)
    Rejected => Left ClosedPathRejected
    Exhausted => Left ClosedPathExhausted

||| Weaken only dimension scope. The underlying closed computational terms
||| and their checked endpoints are unchanged.
weakenClosedPath : CorePathExpr 0 -> CorePathExpr n
weakenClosedPath = substituteCoreDimensions (\i => absurd i)

||| Apply a checked closed path at any scoped interval. This returns raw
||| experimental syntax, not a checked Fibril term, and rechecks the stored path
||| under the supplied budgets before performing capture-avoiding substitution.
export
applyCheckedPathAt : Nat -> Nat -> Nat -> CheckedClosedPath -> ScopedInterval n -> CorePathStep n
applyCheckedPathAt depth reduction fuel (MkCheckedClosedPath path left right) r =
  if pathWithinBudget depth path
    then applyCorePathAt depth reduction fuel (weakenClosedPath path) r left right
    else CoreStepExhausted

||| Apply a checked path at a closed interval. The experimental runner rechecks
||| its recorded inputs with the supplied budgets; exhaustion still fails closed.
export
applyCheckedClosedPath : Nat -> Nat -> Nat -> CheckedClosedPath -> ScopedInterval 0 -> CoreEndpoint
applyCheckedClosedPath depth reduction fuel (MkCheckedClosedPath path left right) r =
  runCorePathExpr depth reduction fuel (CoreApply path r) left right

||| Return the core syntax carried by a checked Boolean. The syntax by itself
||| is not a reusable witness; callers must keep the opaque value for evidence.
export
forgetCheckedClosedBool : CheckedClosedBool -> Term 0
forgetCheckedClosedBool (MkCheckedClosedBool value) = value

||| Check and reduce a checked path at a literal endpoint. Independently recheck
||| the result and compare it to the selected declared boundary before sealing it.
||| All component calls reuse the given budgets independently, not globally.
export
checkPathEndpoint : Nat -> Nat -> Nat -> CheckedClosedPath -> Bool ->
                    Either ClosedPathFailure CheckedClosedBool
checkPathEndpoint depth reduction fuel checked@(MkCheckedClosedPath path left right) endpoint =
  case applyCheckedClosedPath depth reduction fuel checked (if endpoint then One else Zero) of
    CoreRejected => Left ClosedPathRejected
    CoreExhausted => Left ClosedPathExhausted
    CoreValue value =>
      let expected = if endpoint then right else left in
      case checkClosedCorePath depth reduction fuel value expected expected of
        Accepted => Right (MkCheckedClosedBool value)
        Rejected => Left ClosedPathRejected
        Exhausted => Left ClosedPathExhausted
