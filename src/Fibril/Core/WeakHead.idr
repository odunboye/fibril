-- Head-only beta/data-case reduction for shape inspection, separate from full conversion.
-- Uses the nameless substitution described in docs/references.md (DEBRUIJN72).
module Fibril.Core.WeakHead

import Fibril.Core.Term

%default total

||| One head beta/data-case step. Do not inspect binder bodies, annotations, or arguments.
||| A variable-headed application is stuck and needs no head step.
public export
stepHead : Term n -> Maybe (Term n)
stepHead (Apply (Lambda q domain body) argument) =
  Just (instantiateTerm argument body)
stepHead (Apply function argument) =
  map (\next => Apply next argument) (stepHead function)
stepHead (UnitCase UnitValue body) = Just body
stepHead (UnitCase scrutinee body) = map (\next => UnitCase next body) (stepHead scrutinee)
stepHead (BoolCase BoolTrue yes no) = Just yes
stepHead (BoolCase BoolFalse yes no) = Just no
stepHead (BoolCase condition yes no) =
  map (\next => BoolCase next yes no) (stepHead condition)
stepHead _ = Nothing

||| Exposed outer syntax is not necessarily in full beta normal form.
public export
data HeadResult : Nat -> Type where
  HeadForm : Term n -> HeadResult n
  HeadLimit : Term n -> HeadResult n

||| Spend fuel only on head beta/data-case contractions.
||| Exhaustion is explicit; fuel is not a time or memory bound.
public export
weakHead : Nat -> Term n -> HeadResult n
weakHead fuel term =
  case stepHead term of
    Nothing => HeadForm term
    Just next =>
      case fuel of
        Z => HeadLimit term
        S rest => weakHead rest next
