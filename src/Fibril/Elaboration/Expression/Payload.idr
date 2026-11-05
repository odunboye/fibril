-- Conservative character-payload estimates for guarded candidate conversion.
module Fibril.Elaboration.Expression.Payload

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

public export
payloadLimit : Nat
payloadLimit = 8192

cap : Nat -> Nat
cap = min (S payloadLimit)

liftPayload : (Fin n -> Nat) -> Fin (S n) -> Nat
liftPayload env FZ = 0
liftPayload env (FS i) = env i

mutual
  ||| Saturated estimated character payload after variable substitution.
  ||| String length is host-defined work, not a portable byte/time bound.
  public export
  payloadWeight : (Fin n -> Nat) -> Term n -> Nat
  payloadWeight env (Variable i) = cap (env i)
  payloadWeight env (Universe _) = 0
  payloadWeight env UnitType = 0
  payloadWeight env UnitValue = 0
  payloadWeight env BoolType = 0
  payloadWeight env BoolTrue = 0
  payloadWeight env BoolFalse = 0
  payloadWeight env ReadLine = 0
  payloadWeight env (FileHandleValue _) = 0
  payloadWeight env StringType = 0
  payloadWeight env (StringValue value) = cap (length value)
  payloadWeight env (StringAppend a b) = cap (payloadWeight env a + payloadWeight env b)
  payloadWeight env (StringEqual a b) = cap (payloadWeight env a + payloadWeight env b)
  payloadWeight env (NominalType key indices shape) = cap (length key + payloadTerms env indices + payloadWeight env shape)
  payloadWeight env (NominalValue a b) = cap (payloadWeight env a + payloadWeight env b)
  payloadWeight env (NominalCase a b c) = cap (payloadWeight env a + payloadWeight env b + payloadWeight env c)
  payloadWeight env (VariantType arms) = payloadArms env arms
  payloadWeight env (VariantValue ty _ Nothing) = payloadWeight env ty
  payloadWeight env (VariantValue ty _ (Just value)) = cap (payloadWeight env ty + payloadWeight env value)
  payloadWeight env (VariantCase a b branches) = cap (payloadWeight env a + payloadWeight env b + payloadTerms env branches)
  payloadWeight env (BoxType _ a) = payloadWeight env a
  payloadWeight env (BoxValue a b) = cap (payloadWeight env a + payloadWeight env b)
  payloadWeight env (BoxCase a b c) = cap (payloadWeight env a + payloadWeight env b + payloadWeight env c)
  payloadWeight env (WithInputFile result path body) = cap (payloadWeight env result + payloadWeight env path + payloadWeight env body)
  payloadWeight env (IOType a) = payloadWeight env a
  payloadWeight env (FileHandleType region) = payloadWeight env region
  payloadWeight env (IOPure a) = payloadWeight env a
  payloadWeight env (WriteLine a) = payloadWeight env a
  payloadWeight env (IOBind a b c d) = cap (payloadWeight env a + payloadWeight env b + payloadWeight env c + payloadWeight env d)
  payloadWeight env (BoolCase a b c) = cap (payloadWeight env a + payloadWeight env b + payloadWeight env c)
  payloadWeight env (Sigma _ _ a b) = cap (payloadWeight env a + payloadWeight (liftPayload env) b)
  payloadWeight env (PairValue a b c) = cap (payloadWeight env a + payloadWeight env b + payloadWeight env c)
  payloadWeight env (PairCase a b c) = cap (payloadWeight env a + payloadWeight env b + payloadWeight env c)
  payloadWeight env (Pi _ a b) = cap (payloadWeight env a + payloadWeight (liftPayload env) b)
  payloadWeight env (Lambda _ a b) = cap (payloadWeight env a + payloadWeight (liftPayload env) b)
  payloadWeight env (Apply a b) = cap (payloadWeight env a + payloadWeight env b)
  payloadWeight env (UnitCase a b) = cap (payloadWeight env a + payloadWeight env b)

  payloadTerms : (Fin n -> Nat) -> List (Term n) -> Nat
  payloadTerms env [] = 0
  payloadTerms env (x :: xs) = cap (payloadWeight env x + payloadTerms env xs)

  payloadArms : (Fin n -> Nat) -> List (Maybe (Quantity, Term n)) -> Nat
  payloadArms env [] = 0
  payloadArms env (Nothing :: xs) = payloadArms env xs
  payloadArms env (Just (_, ty) :: xs) = cap (payloadWeight env ty + payloadArms env xs)

public export
payloadSize : Term n -> Nat
payloadSize = payloadWeight (const 0)
