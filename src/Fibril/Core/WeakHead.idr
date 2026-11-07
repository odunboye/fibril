-- Head-only beta/data-case reduction for shape inspection, separate from full conversion.
-- Uses the nameless substitution described in docs/references.md (DEBRUIJN72).
module Fibril.Core.WeakHead

import Data.Fin
import public Fibril.Core.Reduction.Work
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Data.Bytes
import Fibril.Core.Reduction

%default total

-- Lift the existing Maybe step result through the chosen work policy.
mapStep : Functor m => (a -> b) -> m (Maybe a) -> m (Maybe b)
mapStep f = map (map f)

-- One head beta/data-case step; force primitive operands as needed.
-- Numeric byte primitives require canonical Nat payloads, including successor
-- tails; those operands use full reduction WITH THE SAME work policy. Other
-- heads do not enter binders. A variable-headed application remains stuck.
public export
stepHeadWithGlobals : NaturalWork m => (Nat -> Maybe (Term 0)) -> Term n -> m (Maybe (Term n))
stepHeadWithGlobals globals (GlobalRef key) = pure (map (rename absurd) (globals key))
stepHeadWithGlobals globals (Apply (Lambda q domain body) argument) =
  pure (Just (instantiateTerm argument body))
stepHeadWithGlobals globals (Apply function argument) =
  mapStep (\next => Apply next argument) (stepHeadWithGlobals globals function)
stepHeadWithGlobals globals (UnitCase UnitValue body) = pure (Just body)
stepHeadWithGlobals globals (UnitCase scrutinee body) = mapStep (\next => UnitCase next body) (stepHeadWithGlobals globals scrutinee)
stepHeadWithGlobals globals (NatRec motive base next NatZero) = pure (Just base)
stepHeadWithGlobals globals (NatRec motive base next (NatSucc value)) = do
  visitSuccessor
  pure (Just (Apply (Apply next value) (NatRec motive base next value)))
stepHeadWithGlobals globals (NatRec motive base next value) = mapStep (NatRec motive base next) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (NatRecRuntime motive base next NatZero) = pure (Just base)
stepHeadWithGlobals globals (NatRecRuntime motive base next (NatSucc value)) = do
  visitSuccessor
  pure (Just (Apply (Apply next value) (NatRecRuntime motive base next value)))
stepHeadWithGlobals globals (NatRecRuntime motive base next value) = mapStep (NatRecRuntime motive base next) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (RecFold motive base next (RecEnd _)) = pure (Just base)
stepHeadWithGlobals globals (RecFold motive base next (RecMore _ tail)) = pure (Just (Apply (Apply next tail) (RecFold motive base next tail)))
stepHeadWithGlobals globals (RecFold motive base next value) = mapStep (RecFold motive base next) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (RecCase motive (RecEnd _) base more) = pure (Just base)
stepHeadWithGlobals globals (RecCase motive (RecMore _ tail) base more) = pure (Just (Apply more tail))
stepHeadWithGlobals globals (RecCase motive value base more) = mapStep (\x => RecCase motive x base more) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (NatCase motive NatZero base more) = pure (Just base)
stepHeadWithGlobals globals (NatCase motive (NatSucc tail) base more) = do
  visitSuccessor
  pure (Just (Apply more tail))
stepHeadWithGlobals globals (NatCase motive value base more) = mapStep (\x => NatCase motive x base more) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (SeqCase motive (SeqNil _) base cons) = pure (Just base)
stepHeadWithGlobals globals (SeqCase motive (SeqCons _ head tail) base cons) = pure (Just (Apply (Apply cons head) tail))
stepHeadWithGlobals globals (SeqCase motive value base cons) = mapStep (\x => SeqCase motive x base cons) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (SeqFold motive base next (SeqNil _)) = pure (Just base)
stepHeadWithGlobals globals (SeqFold motive base next (SeqCons _ head tail)) = pure (Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail)))
stepHeadWithGlobals globals (SeqFold motive base next value) = mapStep (SeqFold motive base next) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (BoolCase BoolTrue yes no) = pure (Just yes)
stepHeadWithGlobals globals (BoolCase BoolFalse yes no) = pure (Just no)
stepHeadWithGlobals globals (BoolCase condition yes no) =
  mapStep (\next => BoolCase next yes no) (stepHeadWithGlobals globals condition)
stepHeadWithGlobals globals (NominalCase motive (NominalValue ty value) branch) = pure (Just (Apply branch value))
stepHeadWithGlobals globals (NominalCase motive value branch) = mapStep (\next => NominalCase motive next branch) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (VariantCase motive (VariantValue ty tag payload) branches) = pure (variantContract tag payload branches)
stepHeadWithGlobals globals (VariantCase motive value branches) = mapStep (\next => VariantCase motive next branches) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (BoxCase motive (BoxValue ty value) branch) = pure (Just (Apply branch value))
stepHeadWithGlobals globals (BoxCase motive value branch) = mapStep (\next => BoxCase motive next branch) (stepHeadWithGlobals globals value)
stepHeadWithGlobals globals (PairCase motive (PairValue ty first second) branch) = pure (Just (Apply (Apply branch first) second))
stepHeadWithGlobals globals (PairCase motive scrutinee branch) = mapStep (\next => PairCase motive next branch) (stepHeadWithGlobals globals scrutinee)
stepHeadWithGlobals globals (IOBind a b (IOPure value) next) = pure (Just (Apply next value))
stepHeadWithGlobals globals (IOBind a b action next) = mapStep (\result => IOBind a b result next) (stepHeadWithGlobals globals action)
stepHeadWithGlobals globals (UTF8Encode (StringValue text)) = pure (Just (encodeUTF8Value text))
stepHeadWithGlobals globals (UTF8Encode x) = mapStep UTF8Encode (stepHeadWithGlobals globals x)
stepHeadWithGlobals globals (UTF8Decode (BytesValue bytes)) = pure (Just (decodeUTF8Value bytes))
stepHeadWithGlobals globals (UTF8Decode x) = mapStep UTF8Decode (stepHeadWithGlobals globals x)
stepHeadWithGlobals globals (BytesLengthIs a b) = do
  reduced <- contractLengthIsWith a b
  case reduced of
    Just result => pure (Just result)
    Nothing => do
      reduced <- stepWithGlobals globals a
      case reduced of
        Just next => pure (Just (BytesLengthIs next b))
        Nothing => mapStep (BytesLengthIs a) (stepHeadWithGlobals globals b)
stepHeadWithGlobals globals (BytesIndex a b) = do
  reduced <- contractIndexWith a b
  case reduced of
    Just result => pure (Just result)
    Nothing => do
      reduced <- stepWithGlobals globals a
      case reduced of
        Just next => pure (Just (BytesIndex next b))
        Nothing => mapStep (BytesIndex a) (stepHeadWithGlobals globals b)
stepHeadWithGlobals globals (BytesSlice a b c) = do
  reduced <- contractSliceWith a b c
  case reduced of
    Just result => pure (Just result)
    Nothing => do
      reduced <- stepWithGlobals globals a
      case reduced of
        Just next => pure (Just (BytesSlice next b c))
        Nothing => do
          reduced <- stepWithGlobals globals b
          case reduced of
            Just next => pure (Just (BytesSlice a next c))
            Nothing => mapStep (BytesSlice a b) (stepHeadWithGlobals globals c)
stepHeadWithGlobals globals (WithRegion _ body) = pure (Just (Apply body UnitType))
stepHeadWithGlobals globals (BytesAppend (BytesValue a) (BytesValue b)) = pure (Just (BytesValue (append a b)))
stepHeadWithGlobals globals (BytesAppend a b) = do
  reduced <- stepHeadWithGlobals globals a
  case reduced of
    Just next => pure (Just (BytesAppend next b))
    Nothing => mapStep (BytesAppend a) (stepHeadWithGlobals globals b)
stepHeadWithGlobals globals (BytesShare (BytesValue value)) = pure (Just (BoxValue (BoxType Unrestricted BytesType) (BytesValue value)))
stepHeadWithGlobals globals (BytesShare x) = mapStep BytesShare (stepHeadWithGlobals globals x)
stepHeadWithGlobals globals (BytesLength (BytesValue value)) = map Just (materializeNatural (byteLength value))
stepHeadWithGlobals globals (BytesLength x) = mapStep BytesLength (stepHeadWithGlobals globals x)
stepHeadWithGlobals globals (BytesOctet x) = do
  reduced <- octetOperand x
  case reduced of
    Just byte => pure (Just (BytesValue (fromList [byte])))
    Nothing => mapStep BytesOctet (stepWithGlobals globals x)
stepHeadWithGlobals globals (StringAppend (StringValue left) (StringValue right)) = pure (Just (StringValue (left ++ right)))
stepHeadWithGlobals globals (StringAppend left right) = do
  reduced <- stepHeadWithGlobals globals left
  case reduced of
    Just next => pure (Just (StringAppend next right))
    Nothing => mapStep (StringAppend left) (stepHeadWithGlobals globals right)
stepHeadWithGlobals globals (StringEqual (StringValue left) (StringValue right)) = pure (Just (if left == right then BoolTrue else BoolFalse))
stepHeadWithGlobals globals (StringEqual left right) = do
  reduced <- stepHeadWithGlobals globals left
  case reduced of
    Just next => pure (Just (StringEqual next right))
    Nothing => mapStep (StringEqual left) (stepHeadWithGlobals globals right)
stepHeadWithGlobals globals _ = pure Nothing

||| Existing unmetered head reduction; no binary count ledger is installed.
public export
stepHead : Term n -> Maybe (Term n)
stepHead term = runIdentity (stepHeadWithGlobals (const Nothing) term)

public export
stepHeadWith : NaturalWork m => Term n -> m (Maybe (Term n))
stepHeadWith = stepHeadWithGlobals (const Nothing)

public export
stepHeadGlobals : (Nat -> Maybe (Term 0)) -> Term n -> Maybe (Term n)
stepHeadGlobals globals term = runIdentity (stepHeadWithGlobals globals term)

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

public export
weakHeadGlobals : (Nat -> Maybe (Term 0)) -> Nat -> Term n -> HeadResult n
weakHeadGlobals globals fuel term =
  case stepHeadGlobals globals term of
    Nothing => HeadForm term
    Just next => case fuel of
      Z => HeadLimit term
      S rest => weakHeadGlobals globals rest next
