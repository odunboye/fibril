module Fibril.Foundation.DeMorgan.Restriction

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| A dimension context's accumulated face assumption, not a term context.
public export
record Restriction (n : Nat) where
  constructor Under
  assumption : ScopedFace n

public export
unrestricted : Restriction n
unrestricted = Under STop

public export
restrict : Restriction n -> ScopedFace n -> Restriction n
restrict (Under current) extra = Under (SConjunction current extra)

||| Entailment under the accumulated face assumptions.
public export
holds : Restriction n -> ScopedFace n -> Bool
holds (Under current) goal = entailsScoped current goal

||| Contradictory restrictions are valid empty faces, not scope errors.
public export
isEmptyRestriction : Restriction n -> Bool
isEmptyRestriction context = holds context SBottom

public export
weakenRestriction : Restriction n -> Restriction (S n)
weakenRestriction (Under current) = Under (weakenFace current)

public export
substituteRestriction : (Fin n -> ScopedInterval m) -> Restriction n -> Restriction m
substituteRestriction env (Under current) = Under (substituteScopedFace env current)
