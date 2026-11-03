-- Partial scope transport used only by the untrusted expression elaborator.
module Fibril.Elaboration.Expression.Scope

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  liftPartial : (Fin n -> Maybe (Fin m)) -> Fin (S n) -> Maybe (Fin (S m))
  liftPartial env FZ = Just FZ
  liftPartial env (FS i) = map FS (env i)

  public export
  thin : (Fin n -> Maybe (Fin m)) -> Term n -> Maybe (Term m)
  thin env (Variable i) = Variable <$> env i
  thin env (Universe level) = Just (Universe level)
  thin env UnitType = Just UnitType
  thin env UnitValue = Just UnitValue
  thin env BoolType = Just BoolType
  thin env BoolTrue = Just BoolTrue
  thin env BoolFalse = Just BoolFalse
  thin env StringType = Just StringType
  thin env (StringValue value) = Just (StringValue value)
  thin env (StringAppend a b) = [| StringAppend (thin env a) (thin env b) |]
  thin env (StringEqual a b) = [| StringEqual (thin env a) (thin env b) |]
  thin env (BoolCase a b c) = [| BoolCase (thin env a) (thin env b) (thin env c) |]
  thin env (IOType a) = IOType <$> thin env a
  thin env (IOPure a) = IOPure <$> thin env a
  thin env (WriteLine a) = WriteLine <$> thin env a
  thin env (IOBind a b c d) = [| IOBind (thin env a) (thin env b) (thin env c) (thin env d) |]
  thin env (NominalType key indices shape) = [| NominalType (pure key) (thinTerms env indices) (thin env shape) |]
  thin env (NominalValue ty value) = [| NominalValue (thin env ty) (thin env value) |]
  thin env (NominalCase motive value branch) = [| NominalCase (thin env motive) (thin env value) (thin env branch) |]
  thin env (VariantType arms) = VariantType <$> thinArms env arms
  thin env (VariantValue ty tag Nothing) = (\next => VariantValue next tag Nothing) <$> thin env ty
  thin env (VariantValue ty tag (Just value)) = [| VariantValue (thin env ty) (pure tag) (Just <$> thin env value) |]
  thin env (VariantCase motive value branches) = [| VariantCase (thin env motive) (thin env value) (thinTerms env branches) |]
  thin env (BoxType q a) = BoxType q <$> thin env a
  thin env (BoxValue a b) = [| BoxValue (thin env a) (thin env b) |]
  thin env (BoxCase a b c) = [| BoxCase (thin env a) (thin env b) (thin env c) |]
  thin env (Sigma q r a b) = [| Sigma (pure q) (pure r) (thin env a) (thin (liftPartial env) b) |]
  thin env (PairValue a b c) = [| PairValue (thin env a) (thin env b) (thin env c) |]
  thin env (PairCase a b c) = [| PairCase (thin env a) (thin env b) (thin env c) |]
  thin env (Pi q a b) = [| Pi (pure q) (thin env a) (thin (liftPartial env) b) |]
  thin env (Lambda q a b) = [| Lambda (pure q) (thin env a) (thin (liftPartial env) b) |]
  thin env (Apply a b) = [| Apply (thin env a) (thin env b) |]
  thin env (UnitCase a b) = [| UnitCase (thin env a) (thin env b) |]

  public export
  dropNewest : Term (S n) -> Maybe (Term n)
  dropNewest = thin (\i => case i of FZ => Nothing; FS outer => Just outer)

  public export
  inferredResultNodes : Nat
  inferredResultNodes = 512

  -- Preserve locally bound variables when estimating a substitution under binders.
  liftWeights : (Fin n -> Nat) -> Fin (S n) -> Nat
  liftWeights env FZ = 1
  liftWeights env (FS i) = env i

  ||| Saturated size of a substitution tree, before building it.
  public export
  substitutionNodes : (Fin n -> Nat) -> Term n -> Nat
  substitutionNodes env (Variable i) = min (S inferredResultNodes) (env i)
  substitutionNodes env (Universe _) = 1
  substitutionNodes env UnitType = 1
  substitutionNodes env UnitValue = 1
  substitutionNodes env BoolType = 1
  substitutionNodes env BoolTrue = 1
  substitutionNodes env BoolFalse = 1
  substitutionNodes env StringType = 1
  substitutionNodes env (StringValue _) = 1
  substitutionNodes env (StringAppend a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b)
  substitutionNodes env (StringEqual a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b)
  substitutionNodes env (BoolCase a b c) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b + substitutionNodes env c)
  substitutionNodes env (IOType a) = min (S inferredResultNodes) (1 + substitutionNodes env a)
  substitutionNodes env (IOPure a) = min (S inferredResultNodes) (1 + substitutionNodes env a)
  substitutionNodes env (WriteLine a) = min (S inferredResultNodes) (1 + substitutionNodes env a)
  substitutionNodes env (IOBind a b c d) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b + substitutionNodes env c + substitutionNodes env d)
  substitutionNodes env (NominalType _ indices shape) = min (S inferredResultNodes) (1 + termNodes env indices + substitutionNodes env shape)
  substitutionNodes env (NominalValue ty value) = min (S inferredResultNodes) (1 + substitutionNodes env ty + substitutionNodes env value)
  substitutionNodes env (NominalCase motive value branch) = min (S inferredResultNodes) (1 + substitutionNodes env motive + substitutionNodes env value + substitutionNodes env branch)
  substitutionNodes env (VariantType arms) = min (S inferredResultNodes) (1 + armNodes env arms)
  substitutionNodes env (VariantValue ty _ Nothing) = min (S inferredResultNodes) (1 + substitutionNodes env ty)
  substitutionNodes env (VariantValue ty _ (Just value)) = min (S inferredResultNodes) (1 + substitutionNodes env ty + substitutionNodes env value)
  substitutionNodes env (VariantCase motive value branches) = min (S inferredResultNodes) (1 + substitutionNodes env motive + substitutionNodes env value + termNodes env branches)
  substitutionNodes env (BoxType _ a) = min (S inferredResultNodes) (1 + substitutionNodes env a)
  substitutionNodes env (BoxValue a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b)
  substitutionNodes env (BoxCase a b c) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b + substitutionNodes env c)
  substitutionNodes env (Sigma _ _ a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes (liftWeights env) b)
  substitutionNodes env (PairValue a b c) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b + substitutionNodes env c)
  substitutionNodes env (PairCase a b c) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b + substitutionNodes env c)
  substitutionNodes env (Pi _ a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes (liftWeights env) b)
  substitutionNodes env (Lambda _ a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes (liftWeights env) b)
  substitutionNodes env (Apply a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b)
  substitutionNodes env (UnitCase a b) = min (S inferredResultNodes) (1 + substitutionNodes env a + substitutionNodes env b)

  public export
  typeNodes : Term n -> Nat
  typeNodes = substitutionNodes (const 1)

  thinArms : (Fin n -> Maybe (Fin m)) -> List (Maybe (Quantity, Term n)) -> Maybe (List (Maybe (Quantity, Term m)))
  thinArms env [] = Just []
  thinArms env (Nothing :: rest) = (Nothing ::) <$> thinArms env rest
  thinArms env (Just (q, ty) :: rest) = do
    next <- thin env ty
    following <- thinArms env rest
    Just (Just (q, next) :: following)

  thinTerms : (Fin n -> Maybe (Fin m)) -> List (Term n) -> Maybe (List (Term m))
  thinTerms env [] = Just []
  thinTerms env (x :: xs) = [| (thin env x) :: (thinTerms env xs) |]

  armNodes : (Fin n -> Nat) -> List (Maybe (Quantity, Term n)) -> Nat
  armNodes env [] = 0
  armNodes env (Nothing :: rest) = min (S inferredResultNodes) (1 + armNodes env rest)
  armNodes env (Just (_, ty) :: rest) = min (S inferredResultNodes) (1 + substitutionNodes env ty + armNodes env rest)

  termNodes : (Fin n -> Nat) -> List (Term n) -> Nat
  termNodes env [] = 0
  termNodes env (x :: xs) = min (S inferredResultNodes) (1 + substitutionNodes env x + termNodes env xs)
