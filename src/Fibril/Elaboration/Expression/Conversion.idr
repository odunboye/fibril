-- Conservative, untrusted conversion for inferred data-case result types.
-- It is not the kernel conversion judgment or an allocation/time guarantee.
module Fibril.Elaboration.Expression.Conversion

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Payload

%default total

-- Short-circuiting structural admission; character payload is checked separately.
mutual
  admit : Nat -> Term n -> Maybe Nat
  admit Z _ = Nothing
  admit (S budget) (Variable _) = Just budget
  admit (S budget) (Universe _) = Just budget
  admit (S budget) UnitType = Just budget
  admit (S budget) UnitValue = Just budget
  admit (S budget) BoolType = Just budget
  admit (S budget) BoolTrue = Just budget
  admit (S budget) BoolFalse = Just budget
  admit (S budget) NatType = Just budget
  admit (S budget) NatZero = Just budget
  admit (S budget) (NatSucc x) = admit budget x
  admit (S budget) (NatRec p z s x) = do a <- admit budget p; b <- admit a z; c <- admit b s; admit c x
  admit (S budget) (NatRecRuntime p z s x) = do a <- admit budget p; b <- admit a z; c <- admit b s; admit c x
  admit (S budget) (RecType _) = Just budget
  admit (S budget) (RecEnd ty) = admit budget ty
  admit (S budget) (RecMore ty x) = do a <- admit budget ty; admit a x
  admit (S budget) (RecFold p z s x) = do a <- admit budget p; b <- admit a z; c <- admit b s; admit c x
  admit (S budget) (RecCase p x z s) = do a <- admit budget p; b <- admit a x; c <- admit b z; admit c s
  admit (S budget) (SeqType _ a) = admit budget a
  admit (S budget) (SeqNil ty) = admit budget ty
  admit (S budget) (SeqCons ty h t) = do a <- admit budget ty; b <- admit a h; admit b t
  admit (S budget) (SeqFold p z s x) = do a <- admit budget p; b <- admit a z; c <- admit b s; admit c x
  admit (S budget) StringType = Just budget
  admit (S budget) (StringValue _) = Just budget
  admit (S budget) (StringAppend a b) = do x <- admit budget a; admit x b
  admit (S budget) (StringEqual a b) = do x <- admit budget a; admit x b
  admit (S budget) (NominalType _ indices shape) = do x <- admitTerms budget indices; admit x shape
  admit (S budget) (NominalValue a b) = do x <- admit budget a; admit x b
  admit (S budget) (NominalCase a b c) = do x <- admit budget a; y <- admit x b; admit y c
  admit (S budget) (VariantType arms) = admitArms budget arms
  admit (S budget) (VariantValue ty _ Nothing) = admit budget ty
  admit (S budget) (VariantValue ty _ (Just value)) = do x <- admit budget ty; admit x value
  admit (S budget) (VariantCase motive value branches) = do x <- admit budget motive; y <- admit x value; admitTerms y branches
  admit (S budget) (BoxType _ a) = admit budget a
  admit (S budget) (BoxValue a b) = do x <- admit budget a; admit x b
  admit (S budget) (BoxCase a b c) = do x <- admit budget a; y <- admit x b; admit y c
  admit (S budget) (IOType a) = admit budget a
  admit (S budget) (IOPure a) = admit budget a
  admit (S budget) (WriteLine a) = admit budget a
  admit (S budget) (IOBind a b c d) = do w <- admit budget a; x <- admit w b; y <- admit x c; admit y d
  admit (S budget) (BoolCase a b c) = do x <- admit budget a; y <- admit x b; admit y c
  admit (S budget) (Sigma _ _ a b) = do x <- admit budget a; admit x b
  admit (S budget) (PairValue a b c) = do x <- admit budget a; y <- admit x b; admit y c
  admit (S budget) (PairCase a b c) = do x <- admit budget a; y <- admit x b; admit y c
  admit (S budget) (Pi _ a b) = do x <- admit budget a; admit x b
  admit (S budget) (Lambda _ a b) = do x <- admit budget a; admit x b
  admit (S budget) (Apply a b) = do x <- admit budget a; admit x b
  admit (S budget) (UnitCase a b) = do x <- admit budget a; admit x b

  admitTerms : Nat -> List (Term n) -> Maybe Nat
  admitTerms budget [] = Just budget
  admitTerms Z (_ :: _) = Nothing
  admitTerms (S budget) (term :: rest) = do x <- admit budget term; admitTerms x rest

  admitArms : Nat -> List (Maybe (Quantity, Term n)) -> Maybe Nat
  admitArms budget [] = Just budget
  admitArms Z (_ :: _) = Nothing
  admitArms (S budget) (Nothing :: rest) = admitArms budget rest
  admitArms (S budget) (Just (_, ty) :: rest) = do x <- admit budget ty; admitArms x rest

-- Check every potential beta redex before using the shared one-step reducer.
-- The whole input size plus the full substituted body is a conservative bound
-- on the next tree, including surrounding context and weakened replacements.
mutual
  safeRedexes : Nat -> Nat -> Term n -> Bool
  safeRedexes size payload (Variable _) = True
  safeRedexes size payload (Universe _) = True
  safeRedexes size payload UnitType = True
  safeRedexes size payload UnitValue = True
  safeRedexes size payload BoolType = True
  safeRedexes size payload BoolTrue = True
  safeRedexes size payload BoolFalse = True
  safeRedexes size payload NatType = True
  safeRedexes size payload NatZero = True
  safeRedexes size payload (NatSucc x) = safeRedexes size payload x
  safeRedexes size payload (NatRec p z s (NatSucc x)) =
    size + typeNodes s + typeNodes x + 2 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize x <= payloadLimit &&
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s && safeRedexes size payload x
  safeRedexes size payload (NatRec p z s x) =
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s && safeRedexes size payload x
  safeRedexes size payload (NatRecRuntime p z s (NatSucc x)) =
    size + typeNodes s + typeNodes x + 2 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize x <= payloadLimit &&
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s && safeRedexes size payload x
  safeRedexes size payload (NatRecRuntime p z s x) =
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s && safeRedexes size payload x
  safeRedexes size payload (RecType _) = True
  safeRedexes size payload (RecEnd ty) = safeRedexes size payload ty
  safeRedexes size payload (RecMore ty x) = safeRedexes size payload ty && safeRedexes size payload x
  safeRedexes size payload (RecFold p z s (RecMore ty x)) =
    size + typeNodes s + typeNodes x + 2 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize x <= payloadLimit &&
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s &&
    safeRedexes size payload ty && safeRedexes size payload x
  safeRedexes size payload (RecFold p z s x) =
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s && safeRedexes size payload x
  -- A recursive-case contraction selects a branch or constructs one Apply;
  -- it duplicates no subtree and is smaller than its already admitted input.
  safeRedexes size payload (RecCase p x z s) =
    safeRedexes size payload p && safeRedexes size payload x && safeRedexes size payload z && safeRedexes size payload s
  safeRedexes size payload (SeqType _ a) = safeRedexes size payload a
  safeRedexes size payload (SeqNil ty) = safeRedexes size payload ty
  safeRedexes size payload (SeqCons ty h t) = safeRedexes size payload ty && safeRedexes size payload h && safeRedexes size payload t
  safeRedexes size payload (SeqFold p z s (SeqCons ty h t)) =
    size + typeNodes s + typeNodes t + 3 <= inferredResultNodes &&
    payload + payloadSize s + payloadSize t <= payloadLimit &&
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s &&
    safeRedexes size payload ty && safeRedexes size payload h && safeRedexes size payload t
  safeRedexes size payload (SeqFold p z s x) =
    safeRedexes size payload p && safeRedexes size payload z && safeRedexes size payload s && safeRedexes size payload x
  safeRedexes size payload StringType = True
  safeRedexes size payload (StringValue _) = True
  safeRedexes size payload (StringAppend a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (StringEqual a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (NominalType _ indices shape) = safeTerms size payload indices && safeRedexes size payload shape
  safeRedexes size payload (NominalValue a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (NominalCase a b c) = safeRedexes size payload a && safeRedexes size payload b && safeRedexes size payload c
  safeRedexes size payload (VariantType arms) = safeArms size payload arms
  safeRedexes size payload (VariantValue ty _ Nothing) = safeRedexes size payload ty
  safeRedexes size payload (VariantValue ty _ (Just value)) = safeRedexes size payload ty && safeRedexes size payload value
  safeRedexes size payload (VariantCase a b branches) = safeRedexes size payload a && safeRedexes size payload b && safeTerms size payload branches
  safeRedexes size payload (BoxType _ a) = safeRedexes size payload a
  safeRedexes size payload (BoxValue a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (BoxCase a b c) = safeRedexes size payload a && safeRedexes size payload b && safeRedexes size payload c
  safeRedexes size payload (IOType a) = safeRedexes size payload a
  safeRedexes size payload (IOPure a) = safeRedexes size payload a
  safeRedexes size payload (WriteLine a) = safeRedexes size payload a
  safeRedexes size payload (IOBind a b c d) = safeRedexes size payload a && safeRedexes size payload b && safeRedexes size payload c && safeRedexes size payload d
  safeRedexes size payload (BoolCase a b c) = safeRedexes size payload a && safeRedexes size payload b && safeRedexes size payload c
  safeRedexes size payload (Sigma _ _ a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (PairValue a b c) = safeRedexes size payload a && safeRedexes size payload b && safeRedexes size payload c
  safeRedexes size payload (PairCase a b c) = safeRedexes size payload a && safeRedexes size payload b && safeRedexes size payload c
  safeRedexes size payload (Pi _ a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (Lambda _ a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (Apply (Lambda q domain body) argument) =
    let weights : Fin (S n) -> Nat
        weights FZ = typeNodes argument
        weights (FS _) = 1
        payloadWeights : Fin (S n) -> Nat
        payloadWeights FZ = payloadSize argument
        payloadWeights (FS _) = 0
     in size + substitutionNodes weights body <= inferredResultNodes &&
        payload + payloadWeight payloadWeights body <= payloadLimit &&
        safeRedexes size payload domain && safeRedexes size payload body && safeRedexes size payload argument
  safeRedexes size payload (Apply a b) = safeRedexes size payload a && safeRedexes size payload b
  safeRedexes size payload (UnitCase a b) = safeRedexes size payload a && safeRedexes size payload b

  safeTerms : Nat -> Nat -> List (Term n) -> Bool
  safeTerms size payload [] = True
  safeTerms size payload (x :: xs) = safeRedexes size payload x && safeTerms size payload xs

  safeArms : Nat -> Nat -> List (Maybe (Quantity, Term n)) -> Bool
  safeArms size payload [] = True
  safeArms size payload (Nothing :: xs) = safeArms size payload xs
  safeArms size payload (Just (_, ty) :: xs) = safeRedexes size payload ty && safeArms size payload xs

||| Pre-step structural and character-payload admission; not a typing judgment.
public export
guardedStepAdmitted : Term n -> Bool
guardedStepAdmitted term = case admit inferredResultNodes term of
  Nothing => False
  Just remaining =>
    let size = minus inferredResultNodes remaining
        payload = payloadSize term in
      size <= 510 && payload <= payloadLimit && safeRedexes size payload term

||| Successful results are normal according to the existing raw reducer.
||| Zero fuel never probes a step. Failure is inconclusive, not inequality.
public export
guardedNormal : Nat -> Term n -> Maybe (Term n)
guardedNormal Z term = Nothing
guardedNormal (S fuel) term =
  if not (guardedStepAdmitted term) then Nothing else
    case step term of
      Nothing => Just term
      Just next => guardedNormal fuel next

||| Direct syntactic equality remains the cheap existing fast path.
public export
guardedEqual : Nat -> Term n -> Term n -> Bool
guardedEqual fuel left right =
  if sameSyntax left right then True else
    case (guardedNormal fuel left, guardedNormal fuel right) of
      (Just x, Just y) => sameSyntax x y
      _ => False
