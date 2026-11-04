-- Conservative, untrusted conversion for inferred data-case result types.
-- It is not the kernel conversion judgment or an allocation/time guarantee.
module Fibril.Elaboration.Expression.Conversion

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Elaboration.Expression.Scope

%default total

-- Short-circuiting structural admission. String operations/literals and
-- nominal keys are deliberately excluded from this new reduction path: node
-- counts alone cannot guard string concatenation or key comparisons.
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
  admit (S budget) StringType = Just budget
  admit (S budget) (StringValue _) = Nothing
  admit (S budget) (StringAppend _ _) = Nothing
  admit (S budget) (StringEqual _ _) = Nothing
  admit (S budget) (NominalType _ _ _) = Nothing
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
  safeRedexes : Nat -> Term n -> Bool
  safeRedexes size (Variable _) = True
  safeRedexes size (Universe _) = True
  safeRedexes size UnitType = True
  safeRedexes size UnitValue = True
  safeRedexes size BoolType = True
  safeRedexes size BoolTrue = True
  safeRedexes size BoolFalse = True
  safeRedexes size StringType = True
  safeRedexes size (StringValue _) = False
  safeRedexes size (StringAppend _ _) = False
  safeRedexes size (StringEqual _ _) = False
  safeRedexes size (NominalType _ _ _) = False
  safeRedexes size (NominalValue a b) = safeRedexes size a && safeRedexes size b
  safeRedexes size (NominalCase a b c) = safeRedexes size a && safeRedexes size b && safeRedexes size c
  safeRedexes size (VariantType arms) = safeArms size arms
  safeRedexes size (VariantValue ty _ Nothing) = safeRedexes size ty
  safeRedexes size (VariantValue ty _ (Just value)) = safeRedexes size ty && safeRedexes size value
  safeRedexes size (VariantCase a b branches) = safeRedexes size a && safeRedexes size b && safeTerms size branches
  safeRedexes size (BoxType _ a) = safeRedexes size a
  safeRedexes size (BoxValue a b) = safeRedexes size a && safeRedexes size b
  safeRedexes size (BoxCase a b c) = safeRedexes size a && safeRedexes size b && safeRedexes size c
  safeRedexes size (IOType a) = safeRedexes size a
  safeRedexes size (IOPure a) = safeRedexes size a
  safeRedexes size (WriteLine a) = safeRedexes size a
  safeRedexes size (IOBind a b c d) = safeRedexes size a && safeRedexes size b && safeRedexes size c && safeRedexes size d
  safeRedexes size (BoolCase a b c) = safeRedexes size a && safeRedexes size b && safeRedexes size c
  safeRedexes size (Sigma _ _ a b) = safeRedexes size a && safeRedexes size b
  safeRedexes size (PairValue a b c) = safeRedexes size a && safeRedexes size b && safeRedexes size c
  safeRedexes size (PairCase a b c) = safeRedexes size a && safeRedexes size b && safeRedexes size c
  safeRedexes size (Pi _ a b) = safeRedexes size a && safeRedexes size b
  safeRedexes size (Lambda _ a b) = safeRedexes size a && safeRedexes size b
  safeRedexes size (Apply (Lambda q domain body) argument) =
    let weights : Fin (S n) -> Nat
        weights FZ = typeNodes argument
        weights (FS _) = 1
     in size + substitutionNodes weights body <= inferredResultNodes &&
        safeRedexes size domain && safeRedexes size body && safeRedexes size argument
  safeRedexes size (Apply a b) = safeRedexes size a && safeRedexes size b
  safeRedexes size (UnitCase a b) = safeRedexes size a && safeRedexes size b

  safeTerms : Nat -> List (Term n) -> Bool
  safeTerms size [] = True
  safeTerms size (x :: xs) = safeRedexes size x && safeTerms size xs

  safeArms : Nat -> List (Maybe (Quantity, Term n)) -> Bool
  safeArms size [] = True
  safeArms size (Nothing :: xs) = safeArms size xs
  safeArms size (Just (_, ty) :: xs) = safeRedexes size ty && safeArms size xs

||| Successful results are normal according to the existing raw reducer.
||| Zero fuel never probes a step. Failure is inconclusive, not inequality.
public export
guardedNormal : Nat -> Term n -> Maybe (Term n)
guardedNormal Z term = Nothing
guardedNormal (S fuel) term = do
  remaining <- admit inferredResultNodes term
  let size = minus inferredResultNodes remaining
  if size > 510 || not (safeRedexes size term) then Nothing else
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
