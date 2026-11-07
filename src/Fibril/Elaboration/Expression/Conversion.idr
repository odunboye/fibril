-- Conservative, untrusted conversion for inferred data-case result types.
-- It is not the kernel conversion judgment or an allocation/time guarantee.
module Fibril.Elaboration.Expression.Conversion

import Data.Fin
import Fibril.Core.Term
import Fibril.Data.Bytes
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Payload

import Fibril.Core.Erased

%default total

-- Short-circuiting structural admission; character payload is checked separately.
mutual
  admitGlobals : GlobalContext -> Nat -> Term n -> Maybe Nat
  admitGlobals shared Z _ = Nothing
  admitGlobals shared (S budget) (GlobalRef _) = Just budget
  admitGlobals shared (S budget) (Variable _) = Just budget
  admitGlobals shared (S budget) (Universe _) = Just budget
  admitGlobals shared (S budget) UnitType = Just budget
  admitGlobals shared (S budget) UnitValue = Just budget
  admitGlobals shared (S budget) BoolType = Just budget
  admitGlobals shared (S budget) BoolTrue = Just budget
  admitGlobals shared (S budget) BoolFalse = Just budget
  admitGlobals shared (S budget) NatType = Just budget
  admitGlobals shared (S budget) NatZero = Just budget
  admitGlobals shared (S budget) (NatSucc x) = admitGlobals shared budget x
  admitGlobals shared (S budget) (NatRec p z s x) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a z; c <- admitGlobals shared b s; admitGlobals shared c x
  admitGlobals shared (S budget) (NatRecRuntime p z s x) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a z; c <- admitGlobals shared b s; admitGlobals shared c x
  admitGlobals shared (S budget) (RecType _) = Just budget
  admitGlobals shared (S budget) (RecEnd ty) = admitGlobals shared budget ty
  admitGlobals shared (S budget) (RecMore ty x) = do a <- admitGlobals shared budget ty; admitGlobals shared a x
  admitGlobals shared (S budget) (RecFold p z s x) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a z; c <- admitGlobals shared b s; admitGlobals shared c x
  admitGlobals shared (S budget) (RecCase p x z s) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a x; c <- admitGlobals shared b z; admitGlobals shared c s
  admitGlobals shared (S budget) (NatCase p x z s) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a x; c <- admitGlobals shared b z; admitGlobals shared c s
  admitGlobals shared (S budget) (SeqCase p x z s) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a x; c <- admitGlobals shared b z; admitGlobals shared c s
  admitGlobals shared (S budget) (SeqType _ a) = admitGlobals shared budget a
  admitGlobals shared (S budget) (SeqNil ty) = admitGlobals shared budget ty
  admitGlobals shared (S budget) (SeqCons ty h t) = do a <- admitGlobals shared budget ty; b <- admitGlobals shared a h; admitGlobals shared b t
  admitGlobals shared (S budget) (SeqFold p z s x) = do a <- admitGlobals shared budget p; b <- admitGlobals shared a z; c <- admitGlobals shared b s; admitGlobals shared c x
  admitGlobals shared (S budget) (IterateBinary stateType resultType count step initial) = do a <- admitGlobals shared budget stateType; b <- admitGlobals shared a resultType; c <- admitGlobals shared b count; d <- admitGlobals shared c step; admitGlobals shared d initial
  admitGlobals shared (S budget) (ReadBytes x) = admitGlobals shared budget x
  admitGlobals shared (S budget) (WriteBytes x) = admitGlobals shared budget x
  admitGlobals shared (S budget) RejectBytes = Just budget
  admitGlobals shared (S budget) FlushBytes = Just budget
  admitGlobals shared (S budget) ReadLine = Just budget
  admitGlobals shared (S budget) (FileHandleValue _ _) = Just budget
  admitGlobals shared (S budget) (ReadInputFile handle) = admitGlobals shared budget handle
  admitGlobals shared (S budget) (BytesLengthIs a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (BytesIndex a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (BytesSlice a b c) = do x <- admitGlobals shared budget a; y <- admitGlobals shared x b; admitGlobals shared y c
  admitGlobals shared (S budget) (UTF8Encode x) = admitGlobals shared budget x
  admitGlobals shared (S budget) (UTF8Decode x) = admitGlobals shared budget x
  admitGlobals shared (S budget) BytesType = Just budget
  admitGlobals shared (S budget) (BytesValue _) = Just budget
  admitGlobals shared (S budget) (BytesShare x) = admitGlobals shared budget x
  admitGlobals shared (S budget) (BytesLength x) = admitGlobals shared budget x
  admitGlobals shared (S budget) (BytesOctet x) = admitGlobals shared budget x
  admitGlobals shared (S budget) (BytesAppend a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (WithRegion a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) StringType = Just budget
  admitGlobals shared (S budget) (StringValue _) = Just budget
  admitGlobals shared (S budget) (StringAppend a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (StringEqual a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (NominalType _ indices shape) = do x <- admitTermsGlobals shared budget indices; admitGlobals shared x shape
  admitGlobals shared (S budget) (NominalValue a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (NominalCase a b c) = do x <- admitGlobals shared budget a; y <- admitGlobals shared x b; admitGlobals shared y c
  admitGlobals shared (S budget) (VariantType arms) = admitArmsGlobals shared budget arms
  admitGlobals shared (S budget) (VariantValue ty _ Nothing) = admitGlobals shared budget ty
  admitGlobals shared (S budget) (VariantValue ty _ (Just value)) = do x <- admitGlobals shared budget ty; admitGlobals shared x value
  admitGlobals shared (S budget) (VariantCase motive value branches) = do x <- admitGlobals shared budget motive; y <- admitGlobals shared x value; admitTermsGlobals shared y branches
  admitGlobals shared (S budget) (BoxType _ a) = admitGlobals shared budget a
  admitGlobals shared (S budget) (BoxValue a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (BoxCase a b c) = do x <- admitGlobals shared budget a; y <- admitGlobals shared x b; admitGlobals shared y c
  admitGlobals shared (S budget) (WithInputFile result path body) = do
    first <- admitGlobals shared budget result
    second <- admitGlobals shared first path
    admitGlobals shared second body
  admitGlobals shared (S budget) (IOType a) = admitGlobals shared budget a
  admitGlobals shared (S budget) (FileHandleType region) = admitGlobals shared budget region
  admitGlobals shared (S budget) (IOPure a) = admitGlobals shared budget a
  admitGlobals shared (S budget) (WriteLine a) = admitGlobals shared budget a
  admitGlobals shared (S budget) (IOBind a b c d) = do w <- admitGlobals shared budget a; x <- admitGlobals shared w b; y <- admitGlobals shared x c; admitGlobals shared y d
  admitGlobals shared (S budget) (BoolCase a b c) = do x <- admitGlobals shared budget a; y <- admitGlobals shared x b; admitGlobals shared y c
  admitGlobals shared (S budget) (Sigma _ _ a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (PairValue a b c) = do x <- admitGlobals shared budget a; y <- admitGlobals shared x b; admitGlobals shared y c
  admitGlobals shared (S budget) (PairCase a b c) = do x <- admitGlobals shared budget a; y <- admitGlobals shared x b; admitGlobals shared y c
  admitGlobals shared (S budget) (Pi _ a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (Lambda _ a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (Fix a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (Apply a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b
  admitGlobals shared (S budget) (UnitCase a b) = do x <- admitGlobals shared budget a; admitGlobals shared x b

  admitTermsGlobals : GlobalContext -> Nat -> List (Term n) -> Maybe Nat
  admitTermsGlobals shared budget [] = Just budget
  admitTermsGlobals shared Z (_ :: _) = Nothing
  admitTermsGlobals shared (S budget) (term :: rest) = do x <- admitGlobals shared budget term; admitTermsGlobals shared x rest

  admitArmsGlobals : GlobalContext -> Nat -> List (Maybe (Quantity, Term n)) -> Maybe Nat
  admitArmsGlobals shared budget [] = Just budget
  admitArmsGlobals shared Z (_ :: _) = Nothing
  admitArmsGlobals shared (S budget) (Nothing :: rest) = admitArmsGlobals shared budget rest
  admitArmsGlobals shared (S budget) (Just (_, ty) :: rest) = do x <- admitGlobals shared budget ty; admitArmsGlobals shared x rest

-- Check every potential beta redex before using the shared one-step reducer.
-- The whole input size plus the full substituted body is a conservative bound
-- on the next tree, including surrounding context and weakened replacements.
mutual
  safeRedexesGlobals : GlobalContext -> Nat -> Nat -> Term n -> Bool
  safeRedexesGlobals shared size payload (GlobalRef key) = case globalValue shared key of
    Nothing => False
    Just body => size + typeNodes body <= inferredResultNodes && payload + payloadSize body <= payloadLimit
  safeRedexesGlobals shared size payload (Variable _) = True
  safeRedexesGlobals shared size payload (Universe _) = True
  safeRedexesGlobals shared size payload UnitType = True
  safeRedexesGlobals shared size payload UnitValue = True
  safeRedexesGlobals shared size payload BoolType = True
  safeRedexesGlobals shared size payload BoolTrue = True
  safeRedexesGlobals shared size payload BoolFalse = True
  safeRedexesGlobals shared size payload NatType = True
  safeRedexesGlobals shared size payload NatZero = True
  safeRedexesGlobals shared size payload (NatSucc x) = safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (NatRec p z s (NatSucc x)) =
    size + typeNodes s + typeNodes x + 2 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize x <= payloadLimit &&
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (NatRec p z s x) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (NatRecRuntime p z s (NatSucc x)) =
    size + typeNodes s + typeNodes x + 2 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize x <= payloadLimit &&
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (NatRecRuntime p z s x) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (RecType _) = True
  safeRedexesGlobals shared size payload (RecEnd ty) = safeRedexesGlobals shared size payload ty
  safeRedexesGlobals shared size payload (RecMore ty x) = safeRedexesGlobals shared size payload ty && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (RecFold p z s (RecMore ty x)) =
    size + typeNodes s + typeNodes x + 2 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize x <= payloadLimit &&
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s &&
    safeRedexesGlobals shared size payload ty && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (RecFold p z s x) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s && safeRedexesGlobals shared size payload x
  -- A recursive-case contraction selects a branch or constructs one Apply;
  -- it duplicates no subtree and is smaller than its already admitted input.
  safeRedexesGlobals shared size payload (RecCase p x z s) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload x && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s
  safeRedexesGlobals shared size payload (NatCase p x z s) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload x && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s
  -- Two applications replace the case and constructor nodes; no subtree is copied.
  safeRedexesGlobals shared size payload (SeqCase p x z s) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload x && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s
  safeRedexesGlobals shared size payload (SeqType _ a) = safeRedexesGlobals shared size payload a
  safeRedexesGlobals shared size payload (SeqNil ty) = safeRedexesGlobals shared size payload ty
  safeRedexesGlobals shared size payload (SeqCons ty h t) = safeRedexesGlobals shared size payload ty && safeRedexesGlobals shared size payload h && safeRedexesGlobals shared size payload t
  safeRedexesGlobals shared size payload (SeqFold p z s (SeqCons ty h t)) =
    size + typeNodes s + typeNodes t + 3 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize t <= payloadLimit &&
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s &&
    safeRedexesGlobals shared size payload ty && safeRedexesGlobals shared size payload h && safeRedexesGlobals shared size payload t
  safeRedexesGlobals shared size payload (SeqFold p z s x) =
    safeRedexesGlobals shared size payload p && safeRedexesGlobals shared size payload z && safeRedexesGlobals shared size payload s && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (IterateBinary stateType resultType count step initial) = safeRedexesGlobals shared size payload stateType && safeRedexesGlobals shared size payload resultType && safeRedexesGlobals shared size payload count && safeRedexesGlobals shared size payload step && safeRedexesGlobals shared size payload initial
  safeRedexesGlobals shared size payload (ReadBytes x) = safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (WriteBytes x) = safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload RejectBytes = True
  safeRedexesGlobals shared size payload FlushBytes = True
  safeRedexesGlobals shared size payload ReadLine = True
  safeRedexesGlobals shared size payload (FileHandleValue _ _) = True
  safeRedexesGlobals shared size payload (ReadInputFile handle) = safeRedexesGlobals shared size payload handle
  safeRedexesGlobals shared size payload (BytesIndex index (BytesValue bytes)) =
    case canonicalNatural index of
      Nothing => safeRedexesGlobals shared size payload index
      Just n => case byteAt n bytes of
        Nothing => True
        Just octet => size + cast octet + 4 <= inferredResultNodes
  safeRedexesGlobals shared size payload (BytesLengthIs a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (BytesIndex a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (BytesSlice a b c) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c
  safeRedexesGlobals shared size payload (UTF8Encode (StringValue text)) = size + 6 <= inferredResultNodes && payload + 3 * length text <= payloadLimit
  safeRedexesGlobals shared size payload (UTF8Encode x) = safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (UTF8Decode x) = size + 6 <= inferredResultNodes && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload BytesType = True
  safeRedexesGlobals shared size payload (BytesValue _) = True
  -- Length expands one literal into a unary natural; admit that allocation
  -- before contracting rather than relying on the following step's node check.
  safeRedexesGlobals shared size payload (BytesLength (BytesValue value)) = size + byteLength value <= inferredResultNodes
  safeRedexesGlobals shared size payload (BytesShare x) = size + 4 <= inferredResultNodes && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (BytesLength x) = safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (BytesOctet x) = payload + 1 <= payloadLimit && safeRedexesGlobals shared size payload x
  safeRedexesGlobals shared size payload (BytesAppend a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (WithRegion a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload StringType = True
  safeRedexesGlobals shared size payload (StringValue _) = True
  safeRedexesGlobals shared size payload (StringAppend a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (StringEqual a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (NominalType _ indices shape) = safeTermsGlobals shared size payload indices && safeRedexesGlobals shared size payload shape
  safeRedexesGlobals shared size payload (NominalValue a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (NominalCase a b c) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c
  safeRedexesGlobals shared size payload (VariantType arms) = safeArmsGlobals shared size payload arms
  safeRedexesGlobals shared size payload (VariantValue ty _ Nothing) = safeRedexesGlobals shared size payload ty
  safeRedexesGlobals shared size payload (VariantValue ty _ (Just value)) = safeRedexesGlobals shared size payload ty && safeRedexesGlobals shared size payload value
  safeRedexesGlobals shared size payload (VariantCase a b branches) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeTermsGlobals shared size payload branches
  safeRedexesGlobals shared size payload (BoxType _ a) = safeRedexesGlobals shared size payload a
  safeRedexesGlobals shared size payload (BoxValue a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (BoxCase a b c) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c
  safeRedexesGlobals shared size payload (WithInputFile result path body) = safeRedexesGlobals shared size payload result && safeRedexesGlobals shared size payload path && safeRedexesGlobals shared size payload body
  safeRedexesGlobals shared size payload (IOType a) = safeRedexesGlobals shared size payload a
  safeRedexesGlobals shared size payload (FileHandleType region) = safeRedexesGlobals shared size payload region
  safeRedexesGlobals shared size payload (IOPure a) = safeRedexesGlobals shared size payload a
  safeRedexesGlobals shared size payload (WriteLine a) = safeRedexesGlobals shared size payload a
  safeRedexesGlobals shared size payload (IOBind a b c d) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c && safeRedexesGlobals shared size payload d
  safeRedexesGlobals shared size payload (BoolCase a b c) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c
  safeRedexesGlobals shared size payload (Sigma _ _ a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (PairValue a b c) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c
  safeRedexesGlobals shared size payload (PairCase a b c) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b && safeRedexesGlobals shared size payload c
  safeRedexesGlobals shared size payload (Pi _ a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (Lambda _ a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (Fix a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (Apply (Lambda q domain body) argument) =
    let weights : Fin (S n) -> Nat
        weights FZ = typeNodes argument
        weights (FS _) = 1
        payloadWeights : Fin (S n) -> Nat
        payloadWeights FZ = payloadSize argument
        payloadWeights (FS _) = 0
     in size + substitutionNodes weights body <= inferredResultNodes &&
        payload + payloadWeight payloadWeights body <= payloadLimit &&
        safeRedexesGlobals shared size payload domain && safeRedexesGlobals shared size payload body && safeRedexesGlobals shared size payload argument
  safeRedexesGlobals shared size payload (Apply a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b
  safeRedexesGlobals shared size payload (UnitCase a b) = safeRedexesGlobals shared size payload a && safeRedexesGlobals shared size payload b

  safeTermsGlobals : GlobalContext -> Nat -> Nat -> List (Term n) -> Bool
  safeTermsGlobals shared size payload [] = True
  safeTermsGlobals shared size payload (x :: xs) = safeRedexesGlobals shared size payload x && safeTermsGlobals shared size payload xs

  safeArmsGlobals : GlobalContext -> Nat -> Nat -> List (Maybe (Quantity, Term n)) -> Bool
  safeArmsGlobals shared size payload [] = True
  safeArmsGlobals shared size payload (Nothing :: xs) = safeArmsGlobals shared size payload xs
  safeArmsGlobals shared size payload (Just (_, ty) :: xs) = safeRedexesGlobals shared size payload ty && safeArmsGlobals shared size payload xs

||| Pre-step structural and character-payload admission; not a typing judgment.
public export
guardedStepAdmittedGlobals : GlobalContext -> Term n -> Bool
guardedStepAdmittedGlobals shared term = case admitGlobals shared inferredResultNodes term of
  Nothing => False
  Just remaining =>
    let size = minus inferredResultNodes remaining
        payload = payloadSize term in
      size <= 510 && payload <= payloadLimit && safeRedexesGlobals shared size payload term

||| Successful results are normal according to the existing raw reducer.
||| Zero fuel never probes a step. Failure is inconclusive, not inequality.
public export
guardedNormalGlobals : GlobalContext -> Nat -> Term n -> Maybe (Term n)
guardedNormalGlobals shared Z term = Nothing
guardedNormalGlobals shared (S fuel) term =
  if not (guardedStepAdmittedGlobals shared term) then Nothing else
    case stepGlobals (globalValue shared) term of
      Nothing => Just term
      Just next => guardedNormalGlobals shared fuel next

||| Direct syntactic equality remains the cheap existing fast path.
public export
guardedEqualGlobals : GlobalContext -> Nat -> Term n -> Term n -> Bool
guardedEqualGlobals shared fuel left right =
  if sameSyntax left right then True else
    case (guardedNormalGlobals shared fuel left, guardedNormalGlobals shared fuel right) of
      (Just x, Just y) => sameSyntax x y
      _ => False

-- Closed-syntax compatibility APIs. Shared programs pass their checked context explicitly.
public export
guardedEqual : Nat -> Term n -> Term n -> Bool
guardedEqual = guardedEqualGlobals emptyGlobals

public export
guardedNormal : Nat -> Term n -> Maybe (Term n)
guardedNormal = guardedNormalGlobals emptyGlobals

public export
guardedStepAdmitted : Term n -> Bool
guardedStepAdmitted = guardedStepAdmittedGlobals emptyGlobals
