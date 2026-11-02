-- Partial scope transport used only by the untrusted expression elaborator.
module Fibril.Elaboration.Expression.Scope

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

liftPartial : (Fin n -> Maybe (Fin m)) -> Fin (S n) -> Maybe (Fin (S m))
liftPartial env FZ = Just FZ
liftPartial env (FS i) = map FS (env i)

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

||| Saturated counting for inference admission, not an allocation guarantee.
public export
typeNodes : Term n -> Nat
typeNodes (Variable _) = 1
typeNodes (Universe _) = 1
typeNodes UnitType = 1
typeNodes UnitValue = 1
typeNodes BoolType = 1
typeNodes BoolTrue = 1
typeNodes BoolFalse = 1
typeNodes StringType = 1
typeNodes (StringValue _) = 1
typeNodes (StringAppend a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (StringEqual a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (BoolCase a b c) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b + typeNodes c)
typeNodes (IOType a) = min (S inferredResultNodes) (1 + typeNodes a)
typeNodes (IOPure a) = min (S inferredResultNodes) (1 + typeNodes a)
typeNodes (WriteLine a) = min (S inferredResultNodes) (1 + typeNodes a)
typeNodes (IOBind a b c d) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b + typeNodes c + typeNodes d)
typeNodes (BoxType _ a) = min (S inferredResultNodes) (1 + typeNodes a)
typeNodes (BoxValue a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (BoxCase a b c) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b + typeNodes c)
typeNodes (Sigma _ _ a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (PairValue a b c) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b + typeNodes c)
typeNodes (PairCase a b c) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b + typeNodes c)
typeNodes (Pi _ a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (Lambda _ a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (Apply a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
typeNodes (UnitCase a b) = min (S inferredResultNodes) (1 + typeNodes a + typeNodes b)
