-- Experimental closed-path judgment, separate from the Fibril core checker.
module Fibril.Foundation.DeMorgan.IndependentPath

import Data.Fin
import Fibril.Core.Term
import Fibril.Foundation.DeMorgan.ClosedPath
import Fibril.Foundation.DeMorgan.ClosedCorePath
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| Opaque evidence of acceptance by the restricted experimental path checker.
||| It is not a Fibril core term or evidence of resource-safe runtime use.
export
data CheckedClosedPath : Type where
  MkCheckedClosedPath : CorePathExpr 0 -> Term 0 -> Term 0 -> CheckedClosedPath

||| Failure cannot represent successful checking. Exhaustion is inconclusive,
||| while rejection covers mismatched or unsupported inputs.
public export
data ClosedPathFailure = ClosedPathRejected | ClosedPathExhausted

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
  applyCorePathAt depth reduction fuel (weakenClosedPath path) r left right

||| Apply a checked path at a closed interval. The experimental runner rechecks
||| its recorded inputs with the supplied budgets; exhaustion still fails closed.
export
applyCheckedClosedPath : Nat -> Nat -> Nat -> CheckedClosedPath -> ScopedInterval 0 -> CoreEndpoint
applyCheckedClosedPath depth reduction fuel (MkCheckedClosedPath path left right) r =
  runCorePathExpr depth reduction fuel (CoreApply path r) left right
