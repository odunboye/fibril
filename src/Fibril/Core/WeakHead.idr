-- Head-only beta/data-case reduction for shape inspection, separate from full conversion.
-- Uses the nameless substitution described in docs/references.md (DEBRUIJN72).
module Fibril.Core.WeakHead

import Fibril.Core.Term
import Fibril.Core.Reduction

%default total

||| One head beta/data-case step. Do not inspect binder bodies or annotations; force primitive operands as needed.
||| A variable-headed application is stuck and needs no head step.
public export
stepHeadWith : (unfold : Bool) -> Term n -> Maybe (Term n)
-- Runtime mode only: unfold a Fix applied at a head position. Type-level callers
-- pass False, so conversion and type exposure never unfold recursion.
stepHeadWith True (Apply fix@(Fix ty body) argument) =
  Just (Apply (instantiateTerm fix body) argument)
stepHeadWith unfold (Apply (Lambda q domain body) argument) =
  Just (instantiateTerm argument body)
stepHeadWith unfold (Apply function argument) =
  map (\next => Apply next argument) (stepHeadWith unfold function)
stepHeadWith unfold (UnitCase UnitValue body) = Just body
stepHeadWith unfold (UnitCase scrutinee body) = map (\next => UnitCase next body) (stepHeadWith unfold scrutinee)
stepHeadWith unfold (NatRec motive base next NatZero) = Just base
stepHeadWith unfold (NatRec motive base next (NatSucc value)) = Just (Apply (Apply next value) (NatRec motive base next value))
stepHeadWith unfold (NatRec motive base next value) = map (NatRec motive base next) (stepHeadWith unfold value)
stepHeadWith unfold (NatRecRuntime motive base next NatZero) = Just base
stepHeadWith unfold (NatRecRuntime motive base next (NatSucc value)) = Just (Apply (Apply next value) (NatRecRuntime motive base next value))
stepHeadWith unfold (NatRecRuntime motive base next value) = map (NatRecRuntime motive base next) (stepHeadWith unfold value)
stepHeadWith unfold (RecFold motive base next (RecEnd _)) = Just base
stepHeadWith unfold (RecFold motive base next (RecMore _ tail)) = Just (Apply (Apply next tail) (RecFold motive base next tail))
stepHeadWith unfold (RecFold motive base next value) = map (RecFold motive base next) (stepHeadWith unfold value)
stepHeadWith unfold (RecCase motive (RecEnd _) base more) = Just base
stepHeadWith unfold (RecCase motive (RecMore _ tail) base more) = Just (Apply more tail)
stepHeadWith unfold (RecCase motive value base more) = map (\x => RecCase motive x base more) (stepHeadWith unfold value)
stepHeadWith unfold (SeqCase motive (SeqNil _) base cons) = Just base
stepHeadWith unfold (SeqCase motive (SeqCons _ head tail) base cons) = Just (Apply (Apply cons head) tail)
stepHeadWith unfold (SeqCase motive value base cons) = map (\x => SeqCase motive x base cons) (stepHeadWith unfold value)
stepHeadWith unfold (SeqFold motive base next (SeqNil _)) = Just base
stepHeadWith unfold (SeqFold motive base next (SeqCons _ head tail)) = Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail))
stepHeadWith unfold (SeqFold motive base next value) = map (SeqFold motive base next) (stepHeadWith unfold value)
stepHeadWith unfold (BoolCase BoolTrue yes no) = Just yes
stepHeadWith unfold (BoolCase BoolFalse yes no) = Just no
stepHeadWith unfold (BoolCase condition yes no) =
  map (\next => BoolCase next yes no) (stepHeadWith unfold condition)
stepHeadWith unfold (NominalCase motive (NominalValue ty value) branch) = Just (Apply branch value)
stepHeadWith unfold (NominalCase motive value branch) = map (\next => NominalCase motive next branch) (stepHeadWith unfold value)
stepHeadWith unfold (VariantCase motive (VariantValue ty tag payload) branches) = variantContract tag payload branches
stepHeadWith unfold (VariantCase motive value branches) = map (\next => VariantCase motive next branches) (stepHeadWith unfold value)
stepHeadWith unfold (BoxCase motive (BoxValue ty value) branch) = Just (Apply branch value)
stepHeadWith unfold (BoxCase motive value branch) = map (\next => BoxCase motive next branch) (stepHeadWith unfold value)
stepHeadWith unfold (PairCase motive (PairValue ty first second) branch) = Just (Apply (Apply branch first) second)
stepHeadWith unfold (PairCase motive scrutinee branch) = map (\next => PairCase motive next branch) (stepHeadWith unfold scrutinee)
stepHeadWith unfold (IOBind a b (IOPure value) next) = Just (Apply next value)
stepHeadWith unfold (IOBind a b action next) = map (\result => IOBind a b result next) (stepHeadWith unfold action)
stepHeadWith unfold (StringAppend (StringValue left) (StringValue right)) = Just (StringValue (left ++ right))
stepHeadWith unfold (StringAppend left right) = case stepHeadWith unfold left of
  Just next => Just (StringAppend next right)
  Nothing => map (StringAppend left) (stepHeadWith unfold right)
stepHeadWith unfold (StringEqual (StringValue left) (StringValue right)) = Just (if left == right then BoolTrue else BoolFalse)
stepHeadWith unfold (StringEqual left right) = case stepHeadWith unfold left of
  Just next => Just (StringEqual next right)
  Nothing => map (StringEqual left) (stepHeadWith unfold right)
stepHeadWith unfold _ = Nothing

||| Type-level head step: Fix stays neutral.
public export
stepHead : Term n -> Maybe (Term n)
stepHead = stepHeadWith False

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
