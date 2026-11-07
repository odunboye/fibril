-- Policies for count-related canonical traversal and unary construction.
-- Ordinary reduction stays unmetered; binary count entry uses one shared ledger.
module Fibril.Core.Reduction.Work

import public Control.Monad.Identity
import Fibril.Core.Term
import Fibril.Data.Bytes

%default total

public export
interface Monad m => NaturalWork m where
  visitSuccessor : m ()
  materializeNatural : Nat -> m (Term n)
  naturalOperand : Term n -> m (Maybe Nat)
  octetOperand : Term n -> m (Maybe Bits8)

public export
NaturalWork Identity where
  visitSuccessor = Id ()
  materializeNatural amount = Id (naturalTerm amount)
  naturalOperand term = Id (canonicalNatural term)
  octetOperand term = Id (canonicalOctet term)

||| Nothing is ledger exhaustion, NOT irreducibility/noncanonical syntax.
public export
record CountWork a where
  constructor CountAction
  runCountWork : Nat -> Maybe (Nat, a)

public export
Functor CountWork where
  map f action = CountAction $ \work => do
    (rest, value) <- runCountWork action work
    Just (rest, f value)

public export
Applicative CountWork where
  pure value = CountAction $ \work => Just (work, value)
  functions <*> arguments = CountAction $ \work => do
    (rest, f) <- runCountWork functions work
    (left, value) <- runCountWork arguments rest
    Just (left, f value)

public export
Monad CountWork where
  action >>= next = CountAction $ \work => do
    (rest, value) <- runCountWork action work
    runCountWork (next value) rest

||| Reserve BEFORE invoking build. The charged amount is the number of new
||| unary successors; their later visits are charged separately by the decoder.
public export
reserveNatural : Nat -> (Nat -> a) -> CountWork a
reserveNatural amount build = CountAction $ \work =>
  if amount <= work then Just (minus work amount, build amount) else Nothing

||| The denial equation holds for ANY builder, without evaluating that builder.
public export
reserveNaturalDenied : (amount, work : Nat) -> (build : Nat -> a) ->
  (amount <= work) = False -> runCountWork (reserveNatural amount build) work = Nothing
reserveNaturalDenied amount work build denied = rewrite denied in Refl

readNatural : Nat -> Term n -> Nat -> Maybe (Nat, Maybe Nat)
readNatural count NatZero work = Just (work, Just count)
readNatural count (NatSucc tail) Z = Nothing
readNatural count (NatSucc tail) (S work) = readNatural (S count) tail work
readNatural count _ work = Just (work, Nothing)

readOctet : Bits8 -> Term n -> Nat -> Maybe (Nat, Maybe Bits8)
readOctet count NatZero work = Just (work, Just count)
readOctet count (NatSucc tail) Z = Nothing
readOctet count (NatSucc tail) (S work) = readOctet (count + 1) tail work
readOctet count _ work = Just (work, Nothing)

public export
NaturalWork CountWork where
  visitSuccessor = CountAction $ \work => case work of
    Z => Nothing
    S rest => Just (rest, ())
  materializeNatural amount = reserveNatural amount naturalTerm
  naturalOperand term = CountAction (readNatural 0 term)
  octetOperand term = CountAction (readOctet 0 term)

public export
contractLengthIsWith : NaturalWork m => Term n -> Term n -> m (Maybe (Term n))
contractLengthIsWith count (BytesValue bytes) = do
  value <- naturalOperand count
  pure (map (\n => if n == byteLength bytes then BoolTrue else BoolFalse) value)
contractLengthIsWith _ _ = pure Nothing

public export
contractIndexWith : NaturalWork m => Term n -> Term n -> m (Maybe (Term n))
contractIndexWith index (BytesValue bytes) = do
  value <- naturalOperand index
  case value of
    Nothing => pure Nothing
    Just n => case byteAt n bytes of
      Nothing => pure (Just (VariantValue byteIndexResultType 0 Nothing))
      Just octet => do
        payload <- materializeNatural (cast octet)
        pure (Just (VariantValue byteIndexResultType 1 (Just payload)))
contractIndexWith _ _ = pure Nothing

public export
contractSliceWith : NaturalWork m => Term n -> Term n -> Term n -> m (Maybe (Term n))
contractSliceWith start count (BytesValue bytes) = do
  offset <- naturalOperand start
  case offset of
    Nothing => pure Nothing
    Just n => do
      capacity <- naturalOperand count
      pure (map (\size => BytesValue (slice n size bytes)) capacity)
contractSliceWith _ _ _ = pure Nothing
