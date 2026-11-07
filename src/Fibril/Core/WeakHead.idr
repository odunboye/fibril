-- Head-only beta/data-case reduction for shape inspection, separate from full conversion.
-- Uses the nameless substitution described in docs/references.md (DEBRUIJN72).
module Fibril.Core.WeakHead

import public Fibril.Core.Reduction.Work
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Data.Bytes
import Fibril.Core.Reduction

%default total

-- Lift the existing Maybe step result through the chosen work policy.
mapStep : Functor m => (a -> b) -> m (Maybe a) -> m (Maybe b)
mapStep f = map (map f)

||| One head beta/data-case step; force primitive operands as needed.
||| Numeric byte primitives require canonical Nat payloads, including successor
||| tails; those operands use full reduction WITH THE SAME work policy. Other
||| heads do not enter binders. A variable-headed application remains stuck.
public export
stepHeadWith : NaturalWork m => Term n -> m (Maybe (Term n))
stepHeadWith (Apply (Lambda q domain body) argument) =
  pure (Just (instantiateTerm argument body))
stepHeadWith (Apply function argument) =
  mapStep (\next => Apply next argument) (stepHeadWith function)
stepHeadWith (UnitCase UnitValue body) = pure (Just body)
stepHeadWith (UnitCase scrutinee body) = mapStep (\next => UnitCase next body) (stepHeadWith scrutinee)
stepHeadWith (NatRec motive base next NatZero) = pure (Just base)
stepHeadWith (NatRec motive base next (NatSucc value)) = do
  visitSuccessor
  pure (Just (Apply (Apply next value) (NatRec motive base next value)))
stepHeadWith (NatRec motive base next value) = mapStep (NatRec motive base next) (stepHeadWith value)
stepHeadWith (NatRecRuntime motive base next NatZero) = pure (Just base)
stepHeadWith (NatRecRuntime motive base next (NatSucc value)) = do
  visitSuccessor
  pure (Just (Apply (Apply next value) (NatRecRuntime motive base next value)))
stepHeadWith (NatRecRuntime motive base next value) = mapStep (NatRecRuntime motive base next) (stepHeadWith value)
stepHeadWith (RecFold motive base next (RecEnd _)) = pure (Just base)
stepHeadWith (RecFold motive base next (RecMore _ tail)) = pure (Just (Apply (Apply next tail) (RecFold motive base next tail)))
stepHeadWith (RecFold motive base next value) = mapStep (RecFold motive base next) (stepHeadWith value)
stepHeadWith (RecCase motive (RecEnd _) base more) = pure (Just base)
stepHeadWith (RecCase motive (RecMore _ tail) base more) = pure (Just (Apply more tail))
stepHeadWith (RecCase motive value base more) = mapStep (\x => RecCase motive x base more) (stepHeadWith value)
stepHeadWith (SeqCase motive (SeqNil _) base cons) = pure (Just base)
stepHeadWith (SeqCase motive (SeqCons _ head tail) base cons) = pure (Just (Apply (Apply cons head) tail))
stepHeadWith (SeqCase motive value base cons) = mapStep (\x => SeqCase motive x base cons) (stepHeadWith value)
stepHeadWith (SeqFold motive base next (SeqNil _)) = pure (Just base)
stepHeadWith (SeqFold motive base next (SeqCons _ head tail)) = pure (Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail)))
stepHeadWith (SeqFold motive base next value) = mapStep (SeqFold motive base next) (stepHeadWith value)
stepHeadWith (BoolCase BoolTrue yes no) = pure (Just yes)
stepHeadWith (BoolCase BoolFalse yes no) = pure (Just no)
stepHeadWith (BoolCase condition yes no) =
  mapStep (\next => BoolCase next yes no) (stepHeadWith condition)
stepHeadWith (NominalCase motive (NominalValue ty value) branch) = pure (Just (Apply branch value))
stepHeadWith (NominalCase motive value branch) = mapStep (\next => NominalCase motive next branch) (stepHeadWith value)
stepHeadWith (VariantCase motive (VariantValue ty tag payload) branches) = pure (variantContract tag payload branches)
stepHeadWith (VariantCase motive value branches) = mapStep (\next => VariantCase motive next branches) (stepHeadWith value)
stepHeadWith (BoxCase motive (BoxValue ty value) branch) = pure (Just (Apply branch value))
stepHeadWith (BoxCase motive value branch) = mapStep (\next => BoxCase motive next branch) (stepHeadWith value)
stepHeadWith (PairCase motive (PairValue ty first second) branch) = pure (Just (Apply (Apply branch first) second))
stepHeadWith (PairCase motive scrutinee branch) = mapStep (\next => PairCase motive next branch) (stepHeadWith scrutinee)
stepHeadWith (IOBind a b (IOPure value) next) = pure (Just (Apply next value))
stepHeadWith (IOBind a b action next) = mapStep (\result => IOBind a b result next) (stepHeadWith action)
stepHeadWith (UTF8Encode (StringValue text)) = pure (Just (encodeUTF8Value text))
stepHeadWith (UTF8Encode x) = mapStep UTF8Encode (stepHeadWith x)
stepHeadWith (UTF8Decode (BytesValue bytes)) = pure (Just (decodeUTF8Value bytes))
stepHeadWith (UTF8Decode x) = mapStep UTF8Decode (stepHeadWith x)
stepHeadWith (BytesLengthIs a b) = do
  reduced <- contractLengthIsWith a b
  case reduced of
    Just result => pure (Just result)
    Nothing => do
      reduced <- stepWith a
      case reduced of
        Just next => pure (Just (BytesLengthIs next b))
        Nothing => mapStep (BytesLengthIs a) (stepHeadWith b)
stepHeadWith (BytesIndex a b) = do
  reduced <- contractIndexWith a b
  case reduced of
    Just result => pure (Just result)
    Nothing => do
      reduced <- stepWith a
      case reduced of
        Just next => pure (Just (BytesIndex next b))
        Nothing => mapStep (BytesIndex a) (stepHeadWith b)
stepHeadWith (BytesSlice a b c) = do
  reduced <- contractSliceWith a b c
  case reduced of
    Just result => pure (Just result)
    Nothing => do
      reduced <- stepWith a
      case reduced of
        Just next => pure (Just (BytesSlice next b c))
        Nothing => do
          reduced <- stepWith b
          case reduced of
            Just next => pure (Just (BytesSlice a next c))
            Nothing => mapStep (BytesSlice a b) (stepHeadWith c)
stepHeadWith (BytesAppend (BytesValue a) (BytesValue b)) = pure (Just (BytesValue (append a b)))
stepHeadWith (BytesAppend a b) = do
  reduced <- stepHeadWith a
  case reduced of
    Just next => pure (Just (BytesAppend next b))
    Nothing => mapStep (BytesAppend a) (stepHeadWith b)
stepHeadWith (BytesShare (BytesValue value)) = pure (Just (BoxValue (BoxType Unrestricted BytesType) (BytesValue value)))
stepHeadWith (BytesShare x) = mapStep BytesShare (stepHeadWith x)
stepHeadWith (BytesLength (BytesValue value)) = map Just (materializeNatural (byteLength value))
stepHeadWith (BytesLength x) = mapStep BytesLength (stepHeadWith x)
stepHeadWith (BytesOctet x) = do
  reduced <- octetOperand x
  case reduced of
    Just byte => pure (Just (BytesValue (fromList [byte])))
    Nothing => mapStep BytesOctet (stepWith x)
stepHeadWith (StringAppend (StringValue left) (StringValue right)) = pure (Just (StringValue (left ++ right)))
stepHeadWith (StringAppend left right) = do
  reduced <- stepHeadWith left
  case reduced of
    Just next => pure (Just (StringAppend next right))
    Nothing => mapStep (StringAppend left) (stepHeadWith right)
stepHeadWith (StringEqual (StringValue left) (StringValue right)) = pure (Just (if left == right then BoolTrue else BoolFalse))
stepHeadWith (StringEqual left right) = do
  reduced <- stepHeadWith left
  case reduced of
    Just next => pure (Just (StringEqual next right))
    Nothing => mapStep (StringEqual left) (stepHeadWith right)
stepHeadWith _ = pure Nothing

||| Existing unmetered head reduction; no binary count ledger is installed.
public export
stepHead : Term n -> Maybe (Term n)
stepHead term = runIdentity (stepHeadWith term)

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
