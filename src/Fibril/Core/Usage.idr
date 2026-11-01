-- Usage-vector infrastructure, not term typing or cubical resource rules.
-- Theory: ATKEY18 sections 2.1.1–2.1.3; see docs/references.md.
module Fibril.Core.Usage

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity

%default total

||| Whether a judgment constructs erased or runtime-relevant information.
||| Unrestricted is a binder coefficient, not a third judgment mode.
public export
data Mode = ErasedMode | RuntimeMode

||| Coefficient used for the result of the proposed judgment.
public export
modeCoefficient : Mode -> Quantity
modeCoefficient ErasedMode = Erased
modeCoefficient RuntimeMode = Linear

||| One coefficient per term variable, newest first.
||| The length guarantees scope alignment, not matching context types.
public export
Usage : Nat -> Type
Usage n = Vect n Quantity

||| No computational resources are consumed.
public export
zeroUsage : {n : Nat} -> Usage n
zeroUsage = replicate n Erased

||| Pointwise addition for simultaneously evaluated subterms.
||| Do not use this blindly for alternatives or cubical boundary systems.
public export
combineUsage : Usage n -> Usage n -> Usage n
combineUsage = zipWith add

||| Pointwise least common permission for alternative branches.
||| Unlike addition, joining two exact-once uses remains exact-once.
public export
joinUsage : Usage n -> Usage n -> Usage n
joinUsage = zipWith joinQuantity

||| Scale resource requirements, for example by an application binder quantity.
public export
scaleUsage : Quantity -> Usage n -> Usage n
scaleUsage q = map (multiply q)

||| A variable contributes the judgment's coefficient at its own index.
public export
variableUsage : {n : Nat} -> Mode -> Fin n -> Usage n
variableUsage mode i = replaceAt i (modeCoefficient mode) zeroUsage

||| The coefficient mismatch at the binder currently being discharged.
||| Source locations and binder names belong in later checker diagnostics.
public export
record UsageMismatch where
  constructor Mismatch
  expected : Quantity
  observed : Quantity

||| Erased judgments ignore runtime coefficients but still require type checking.
||| Runtime judgments use the proposed local exact-use binder policy.
public export
discharge : Mode -> Quantity -> Usage (S n) -> Either UsageMismatch (Usage n)
discharge mode binder (used :: rest) =
  let expected = multiply (modeCoefficient mode) binder
   in if allows expected used
         then Right rest
         else Left (Mismatch expected used)
