-- Face assumptions for a dimension context. Empty restrictions are legitimate;
-- this module does not supply arbitrary propositions or term typing.
-- Theory: CCHM18 (face-restricted contexts); this is not the complete context judgment.
-- Bibliography and limitations: docs/references.md.
module Fibril.Foundation.DeMorgan.Restriction

import Data.Fin
import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.Scope

%default total

||| A dimension context's accumulated face assumption, not a term context.
public export
record Restriction (n : Nat) where
  constructor Under
  ||| The accumulated face condition; it may denote the empty face.
  assumption : ScopedFace n

||| The full cube: no additional face assumption.
public export
unrestricted : Restriction n
unrestricted = Under STop

||| Conjoin an assumption, allowing contradictory (empty) restrictions.
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

||| Extend the dimension context, preserving existing assumptions by shifting.
public export
weakenRestriction : Restriction n -> Restriction (S n)
weakenRestriction (Under current) = Under (weakenFace current)

||| Reindex all assumptions through a scope-preserving interval substitution.
public export
substituteRestriction : (Fin n -> ScopedInterval m) -> Restriction n -> Restriction m
substituteRestriction env (Under current) = Under (substituteScopedFace env current)
