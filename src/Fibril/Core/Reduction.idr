-- Reference beta reduction for ordinary scoped syntax, not a typed evaluator.
-- Binding background: DEBRUIJN72; see docs/references.md and docs/reduction.md.
module Fibril.Core.Reduction

import Fibril.Core.Term

%default total

||| One leftmost full beta step, including domain annotations and binder bodies.
||| Nothing means beta normal form for this grammar, not well typed or valid.
public export
step : Term n -> Maybe (Term n)
step (Variable i) = Nothing
step (Universe l) = Nothing
step (Pi q domain body) =
  case step domain of
    Just next => Just (Pi q next body)
    Nothing => map (Pi q domain) (step body)
step (Lambda q domain body) =
  case step domain of
    Just next => Just (Lambda q next body)
    Nothing => map (Lambda q domain) (step body)
step (Apply (Lambda q domain body) argument) =
  Just (instantiateTerm argument body)
step (Apply function argument) =
  case step function of
    Just next => Just (Apply next argument)
    Nothing => map (Apply function) (step argument)

||| Bounded reduction either reaches a normal form or retains unfinished syntax.
public export
data ReductionResult : Nat -> Type where
  Normal : Term n -> ReductionResult n
  OutOfFuel : Term n -> ReductionResult n

||| Fuel bounds beta steps, not time, allocation, or term size.
||| Even at zero fuel, a normal input is recognized by inspecting its next step.
public export
normalize : Nat -> Term n -> ReductionResult n
normalize fuel term =
  case step term of
    Nothing => Normal term
    Just next =>
      case fuel of
        Z => OutOfFuel term
        S rest => normalize rest next

||| Reference beta-conversion outcome; no eta or cubical conversion is included.
public export
data ConversionResult = EqualNormalForms | DifferentNormalForms | Inconclusive

||| Normalize each input with its own budget; exhaustion never means inequality.
||| This is not yet the language's definitional equality judgment.
public export
betaCompare : Nat -> Term n -> Term n -> ConversionResult
betaCompare fuel left right =
  case (normalize fuel left, normalize fuel right) of
    (Normal x, Normal y) =>
      if sameSyntax x y then EqualNormalForms else DifferentNormalForms
    _ => Inconclusive
