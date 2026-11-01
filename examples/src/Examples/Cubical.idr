module Examples.Cubical

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Face

%default total

||| A genuine structural proof about the current implementation's syntax.
||| This is Idris equality, not yet a Fibril cubical path.
public export
substitutionIdentity : (term : Interval Nat) -> substitute Var term = term
substitutionIdentity Zero = Refl
substitutionIdentity One = Refl
substitutionIdentity (Var n) = Refl
substitutionIdentity (Reverse x) = cong Reverse (substitutionIdentity x)
substitutionIdentity (Meet x y) =
  rewrite substitutionIdentity x in
  rewrite substitutionIdentity y in Refl
substitutionIdentity (Join x y) =
  rewrite substitutionIdentity x in
  rewrite substitutionIdentity y in Refl

||| An executable check, not a proof of the normalizer's correctness.
public export
deMorganCheck : Bool
deMorganCheck =
  equivalent (Reverse (Meet (Var 0) (Var 1)))
             (Join (Reverse (Var 0)) (Reverse (Var 1)))

public export
boundaryCheck : Bool
boundaryCheck =
  equivalentFace (Conjunction (Endpoint 0 False) (Endpoint 0 True)) Bottom &&
  not (equivalentFace (Disjunction (Endpoint 0 False) (Endpoint 0 True)) Top)
