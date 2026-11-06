-- Experimental closed-path judgment, separate from the Fibril core checker.
module Fibril.Foundation.DeMorgan.IndependentPath

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

||| Reject unsupported inputs and propagate exhausted checks without producing
||| a witness. The witness records exactly the checked expression and endpoints.
export
checkClosedPath : Nat -> Nat -> Nat -> CorePathExpr 0 -> Term 0 -> Term 0 ->
                  Either PathCheck CheckedClosedPath
checkClosedPath depth reduction fuel path left right =
  case checkCorePathExpr depth reduction fuel path left right of
    Accepted => Right (MkCheckedClosedPath path left right)
    Rejected => Left Rejected
    Exhausted => Left Exhausted

||| Apply a checked path at a closed interval. The experimental runner rechecks
||| its recorded inputs with the supplied budgets; exhaustion still fails closed.
export
applyCheckedClosedPath : Nat -> Nat -> Nat -> CheckedClosedPath -> ScopedInterval 0 -> CoreEndpoint
applyCheckedClosedPath depth reduction fuel (MkCheckedClosedPath path left right) r =
  runCorePathExpr depth reduction fuel (CoreApply path r) left right
