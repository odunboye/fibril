-- Fuel algebra for the actual bounded reference normalizer, checked by Idris 2.
-- No normalization, typing, quantitative preservation, or time-bound claim.
module Fibril.Core.Reduction.Fuel

import Fibril.Core.Term
import Fibril.Core.Reduction

%default total

||| Continue raw normalization-result data with an additional budget.
||| A caller-constructed Normal tag is not checked; the laws below concern results
||| produced by normalize, not arbitrary tags as certificates of normality.
public export
continueNormalization : Nat -> ReductionResult n -> ReductionResult n
continueNormalization extra (Normal result) = Normal result
continueNormalization extra (OutOfFuel pending) = normalize extra pending

stopped : (fuel : Nat) -> (term : Term n) -> step term = Nothing ->
          normalize fuel term = Normal term
stopped fuel term transition = rewrite transition in Refl

exhausted : (term, next : Term n) -> step term = Just next ->
            normalize 0 term = OutOfFuel term
exhausted term next transition = rewrite transition in Refl

advanced : (fuel : Nat) -> (term, next : Term n) -> step term = Just next ->
           normalize (S fuel) term = normalize fuel next
advanced fuel term next transition = rewrite transition in Refl

mutual
  ||| Splitting fuel agrees with continuing the exact result of the first run.
  ||| No termination premise or well-typedness assumption is required.
  public export
  normalizeSplit : (first, second : Nat) -> (term : Term n) ->
                   normalize (first + second) term =
                     continueNormalization second (normalize first term)
  normalizeSplit first second term = splitAt first second term (step term) Refl

  splitAt : (first, second : Nat) -> (term : Term n) ->
            (next : Maybe (Term n)) -> step term = next ->
            normalize (first + second) term =
              continueNormalization second (normalize first term)
  splitAt first second term Nothing transition =
    trans (stopped (first + second) term transition)
          (sym (cong (continueNormalization second) (stopped first term transition)))
  splitAt Z second term (Just next) transition =
    sym (cong (continueNormalization second) (exhausted term next transition))
  splitAt (S first) second term (Just next) transition =
    trans (advanced (first + second) term next transition)
      (trans (normalizeSplit first second next)
             (cong (continueNormalization second)
                   (sym (advanced first term next transition))))

||| Additional fuel cannot undo successful normalization or change its result.
public export
normalizeMore : (fuel, extra : Nat) -> (term, result : Term n) ->
                normalize fuel term = Normal result ->
                normalize (fuel + extra) term = Normal result
normalizeMore fuel extra term result finished =
  trans (normalizeSplit fuel extra term) (rewrite finished in Refl)

||| Continue the exact pending syntax returned by an exhausted run.
||| This is equality of raw evaluator results, not a resource/certificate claim.
public export
normalizeResume : (fuel, extra : Nat) -> (term, pending : Term n) ->
                  normalize fuel term = OutOfFuel pending ->
                  normalize (fuel + extra) term = normalize extra pending
normalizeResume fuel extra term pending unfinished =
  trans (normalizeSplit fuel extra term) (rewrite unfinished in Refl)

normalInjective : {left, right : Term n} -> Normal left = Normal right -> left = right
normalInjective Refl = Refl

outNotNormal : {pending, result : Term n} -> OutOfFuel pending = Normal result -> Void
outNotNormal Refl impossible

mutual
  ||| A Normal result actually produced by normalize has no next reference step.
  ||| Arbitrary caller-constructed Normal tags do not satisfy this premise.
  public export
  normalHasNoStep : (fuel : Nat) -> (term, result : Term n) ->
                    normalize fuel term = Normal result -> step result = Nothing
  normalHasNoStep fuel term result finished =
    noStepAt fuel term result (step term) Refl finished

  noStepAt : (fuel : Nat) -> (term, result : Term n) ->
             (next : Maybe (Term n)) -> step term = next ->
             normalize fuel term = Normal result -> step result = Nothing
  noStepAt fuel term result Nothing transition finished =
    let same = normalInjective (trans (sym (stopped fuel term transition)) finished)
     in rewrite sym same in transition
  noStepAt Z term result (Just next) transition finished =
    void (outNotNormal (trans (sym (exhausted term next transition)) finished))
  noStepAt (S fuel) term result (Just next) transition finished =
    normalHasNoStep fuel next result
      (trans (sym (advanced fuel term next transition)) finished)
