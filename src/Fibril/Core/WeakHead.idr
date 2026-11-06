-- Head-only beta/data-case reduction for shape inspection, separate from full conversion.
-- Uses the nameless substitution described in docs/references.md (DEBRUIJN72).
module Fibril.Core.WeakHead

import Fibril.Core.Term
import Fibril.Data.Bytes
import Fibril.Core.Reduction

%default total

||| One head beta/data-case step. Do not inspect binder bodies or annotations; force primitive operands as needed.
||| A variable-headed application is stuck and needs no head step.
public export
stepHead : Term n -> Maybe (Term n)
stepHead (Apply (Lambda q domain body) argument) =
  Just (instantiateTerm argument body)
stepHead (Apply function argument) =
  map (\next => Apply next argument) (stepHead function)
stepHead (UnitCase UnitValue body) = Just body
stepHead (UnitCase scrutinee body) = map (\next => UnitCase next body) (stepHead scrutinee)
stepHead (NatRec motive base next NatZero) = Just base
stepHead (NatRec motive base next (NatSucc value)) = Just (Apply (Apply next value) (NatRec motive base next value))
stepHead (NatRec motive base next value) = map (NatRec motive base next) (stepHead value)
stepHead (NatRecRuntime motive base next NatZero) = Just base
stepHead (NatRecRuntime motive base next (NatSucc value)) = Just (Apply (Apply next value) (NatRecRuntime motive base next value))
stepHead (NatRecRuntime motive base next value) = map (NatRecRuntime motive base next) (stepHead value)
stepHead (RecFold motive base next (RecEnd _)) = Just base
stepHead (RecFold motive base next (RecMore _ tail)) = Just (Apply (Apply next tail) (RecFold motive base next tail))
stepHead (RecFold motive base next value) = map (RecFold motive base next) (stepHead value)
stepHead (RecCase motive (RecEnd _) base more) = Just base
stepHead (RecCase motive (RecMore _ tail) base more) = Just (Apply more tail)
stepHead (RecCase motive value base more) = map (\x => RecCase motive x base more) (stepHead value)
stepHead (SeqCase motive (SeqNil _) base cons) = Just base
stepHead (SeqCase motive (SeqCons _ head tail) base cons) = Just (Apply (Apply cons head) tail)
stepHead (SeqCase motive value base cons) = map (\x => SeqCase motive x base cons) (stepHead value)
stepHead (SeqFold motive base next (SeqNil _)) = Just base
stepHead (SeqFold motive base next (SeqCons _ head tail)) = Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail))
stepHead (SeqFold motive base next value) = map (SeqFold motive base next) (stepHead value)
stepHead (BoolCase BoolTrue yes no) = Just yes
stepHead (BoolCase BoolFalse yes no) = Just no
stepHead (BoolCase condition yes no) =
  map (\next => BoolCase next yes no) (stepHead condition)
stepHead (NominalCase motive (NominalValue ty value) branch) = Just (Apply branch value)
stepHead (NominalCase motive value branch) = map (\next => NominalCase motive next branch) (stepHead value)
stepHead (VariantCase motive (VariantValue ty tag payload) branches) = variantContract tag payload branches
stepHead (VariantCase motive value branches) = map (\next => VariantCase motive next branches) (stepHead value)
stepHead (BoxCase motive (BoxValue ty value) branch) = Just (Apply branch value)
stepHead (BoxCase motive value branch) = map (\next => BoxCase motive next branch) (stepHead value)
stepHead (PairCase motive (PairValue ty first second) branch) = Just (Apply (Apply branch first) second)
stepHead (PairCase motive scrutinee branch) = map (\next => PairCase motive next branch) (stepHead scrutinee)
stepHead (IOBind a b (IOPure value) next) = Just (Apply next value)
stepHead (IOBind a b action next) = map (\result => IOBind a b result next) (stepHead action)
stepHead (BytesAppend (BytesValue a) (BytesValue b)) = Just (BytesValue (append a b))
stepHead (BytesAppend a b) = case stepHead a of
  Just next => Just (BytesAppend next b)
  Nothing => map (BytesAppend a) (stepHead b)
stepHead (BytesLength (BytesValue value)) = Just (naturalTerm (byteLength value))
stepHead (BytesLength x) = map BytesLength (stepHead x)
stepHead (BytesOctet x) = case canonicalOctet x of
  Just byte => Just (BytesValue (fromList [byte]))
  Nothing => map BytesOctet (stepHead x)
stepHead (StringAppend (StringValue left) (StringValue right)) = Just (StringValue (left ++ right))
stepHead (StringAppend left right) = case stepHead left of
  Just next => Just (StringAppend next right)
  Nothing => map (StringAppend left) (stepHead right)
stepHead (StringEqual (StringValue left) (StringValue right)) = Just (if left == right then BoolTrue else BoolFalse)
stepHead (StringEqual left right) = case stepHead left of
  Just next => Just (StringEqual next right)
  Nothing => map (StringEqual left) (stepHead right)
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
