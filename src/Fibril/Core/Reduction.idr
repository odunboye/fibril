-- Reference beta/data-case reduction for ordinary scoped syntax, not a typed evaluator.
-- Binding background: DEBRUIJN72; see docs/references.md and docs/reduction.md.
module Fibril.Core.Reduction

import Fibril.Core.Term

%default total

||| One leftmost full beta/data-case step, including domain annotations and binder bodies.
||| Nothing means reference normal form for this grammar, not well typed or valid.
public export
step : Term n -> Maybe (Term n)
step (Variable i) = Nothing
step (Universe l) = Nothing
step UnitType = Nothing
step UnitValue = Nothing
step BoolType = Nothing
step BoolTrue = Nothing
step BoolFalse = Nothing
step StringType = Nothing
step (StringValue _) = Nothing
step (StringAppend (StringValue left) (StringValue right)) = Just (StringValue (left ++ right))
step (StringAppend left right) = case step left of
  Just next => Just (StringAppend next right)
  Nothing => map (StringAppend left) (step right)
step (StringEqual (StringValue left) (StringValue right)) = Just (if left == right then BoolTrue else BoolFalse)
step (StringEqual left right) = case step left of
  Just next => Just (StringEqual next right)
  Nothing => map (StringEqual left) (step right)
step (IOType ty) = map IOType (step ty)
step (IOPure value) = map IOPure (step value)
step (WriteLine text) = map WriteLine (step text)
step (IOBind a b (IOPure value) next) = Just (Apply next value)
step (IOBind a b action next) =
  case step a of
    Just result => Just (IOBind result b action next)
    Nothing => case step b of
      Just result => Just (IOBind a result action next)
      Nothing => case step action of
        Just result => Just (IOBind a b result next)
        Nothing => map (IOBind a b action) (step next)
step (BoolCase BoolTrue yes no) = Just yes
step (BoolCase BoolFalse yes no) = Just no
step (BoolCase condition yes no) =
  case step condition of
    Just next => Just (BoolCase next yes no)
    Nothing => case step yes of
      Just next => Just (BoolCase condition next no)
      Nothing => map (BoolCase condition yes) (step no)
step (Sigma q r domain body) =
  case step domain of
    Just next => Just (Sigma q r next body)
    Nothing => map (Sigma q r domain) (step body)
step (PairCase motive (PairValue ty first second) branch) = Just (Apply (Apply branch first) second)
step (PairCase motive scrutinee branch) =
  case step motive of
    Just next => Just (PairCase next scrutinee branch)
    Nothing => case step scrutinee of
      Just next => Just (PairCase motive next branch)
      Nothing => map (PairCase motive scrutinee) (step branch)
step (PairValue ty first second) =
  case step ty of
    Just next => Just (PairValue next first second)
    Nothing => case step first of
      Just next => Just (PairValue ty next second)
      Nothing => map (PairValue ty first) (step second)
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

step (UnitCase UnitValue body) = Just body
step (UnitCase scrutinee body) =
  case step scrutinee of
    Just next => Just (UnitCase next body)
    Nothing => map (UnitCase scrutinee) (step body)

||| Bounded reduction either reaches a normal form or retains unfinished syntax.
public export
data ReductionResult : Nat -> Type where
  Normal : Term n -> ReductionResult n
  OutOfFuel : Term n -> ReductionResult n

||| Fuel bounds beta/data-case contractions, not time, allocation, or term size.
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

||| Reference beta/data-case conversion outcome; no eta or cubical conversion is included.
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
