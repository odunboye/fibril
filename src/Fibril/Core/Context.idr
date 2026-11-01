-- Scope-correct telescopes and usage validation, not context formation checking.
-- Theory: ATKEY18 sec. 2.1.3; DEBRUIJN72. See docs/references.md.
module Fibril.Core.Context

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Usage

%default total

||| A telescope: each domain is scoped over only the preceding entries.
||| Constructors do not establish that stored domains are types.
public export
data Context : Nat -> Type where
  Empty : Context 0
  Extend : Context n -> Quantity -> Term n -> Context (S n)

||| Look up a variable's domain in the full current scope.
||| Weakening accounts for both its own binder and any newer entries.
public export
lookupType : Fin n -> Context n -> Term n
lookupType FZ (Extend rest q domain) = weaken domain
lookupType (FS i) (Extend rest q domain) = weaken (lookupType i rest)

||| Read a binder's declared coefficient without changing it for judgment mode.
public export
lookupQuantity : Fin n -> Context n -> Quantity
lookupQuantity FZ (Extend rest q domain) = q
lookupQuantity (FS i) (Extend rest q domain) = lookupQuantity i rest

||| The first invalid coefficient, with its newest-first context index.
public export
record ContextUsageError (n : Nat) where
  constructor AtVariable
  variable : Fin n
  mismatch : UsageMismatch

||| Validate all coefficients against the proposed local binder policy.
||| In erased mode every observed coefficient must be zero.
||| This checks resource coefficients, not domains, conversion, or cubical rules.
public export
validateUsage : Mode -> Context n -> Usage n -> Either (ContextUsageError n) ()
validateUsage mode Empty [] = Right ()
validateUsage mode (Extend rest q domain) (used :: remaining) =
  let expected = multiply (modeCoefficient mode) q
   in if allows expected used
         then case validateUsage mode rest remaining of
                Right () => Right ()
                Left err => Left (AtVariable (FS err.variable) err.mismatch)
         else Left (AtVariable FZ (Mismatch expected used))
