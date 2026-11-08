-- One scope-preserving traversal for environment-local global references.
module Fibril.Core.GlobalTraversal

import Data.Fin
import Fibril.Data.Bytes
import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  public export
  traverseGlobalRefs : Applicative f => (Nat -> f (Term 0)) -> Term n -> f (Term n)
  traverseGlobalRefs resolve (Variable a0) = [| Variable (pure a0) |]
  traverseGlobalRefs resolve (GlobalRef a0) = map (rename absurd) (resolve a0)
  traverseGlobalRefs resolve (Universe a0) = [| Universe (pure a0) |]
  traverseGlobalRefs resolve UnitType = pure UnitType
  traverseGlobalRefs resolve UnitValue = pure UnitValue
  traverseGlobalRefs resolve BoolType = pure BoolType
  traverseGlobalRefs resolve BoolTrue = pure BoolTrue
  traverseGlobalRefs resolve BoolFalse = pure BoolFalse
  traverseGlobalRefs resolve NatType = pure NatType
  traverseGlobalRefs resolve NatZero = pure NatZero
  traverseGlobalRefs resolve (NatSucc a0) = [| NatSucc (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (NatRec a0 a1 a2 a3) = [| NatRec (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (NatRecRuntime a0 a1 a2 a3) = [| NatRecRuntime (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (RecType a0) = [| RecType (pure a0) |]
  traverseGlobalRefs resolve (RecEnd a0) = [| RecEnd (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (RecMore a0 a1) = [| RecMore (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (RecFold a0 a1 a2 a3) = [| RecFold (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (RecCase a0 a1 a2 a3) = [| RecCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (NatCase a0 a1 a2 a3) = [| NatCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (SeqType a0 a1) = [| SeqType (pure a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (SeqNil a0) = [| SeqNil (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (SeqCons a0 a1 a2) = [| SeqCons (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (SeqFold a0 a1 a2 a3) = [| SeqFold (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (SeqCase a0 a1 a2 a3) = [| SeqCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (UTF8Encode a0) = [| UTF8Encode (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (UTF8Decode a0) = [| UTF8Decode (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve BytesType = pure BytesType
  traverseGlobalRefs resolve (BytesValue a0) = [| BytesValue (pure a0) |]
  traverseGlobalRefs resolve (BytesAppend a0 a1) = [| BytesAppend (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (WithRegion a0 a1) = [| WithRegion (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (BytesShare a0) = [| BytesShare (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (BytesLength a0) = [| BytesLength (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (BytesLengthIs a0 a1) = [| BytesLengthIs (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (BytesIndex a0 a1) = [| BytesIndex (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (BytesSlice a0 a1 a2) = [| BytesSlice (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (BytesOctet a0) = [| BytesOctet (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve StringType = pure StringType
  traverseGlobalRefs resolve (StringValue a0) = [| StringValue (pure a0) |]
  traverseGlobalRefs resolve (StringAppend a0 a1) = [| StringAppend (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (StringEqual a0 a1) = [| StringEqual (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (Prim a0 a1) = [| Prim (pure a0) (traverseTerms resolve a1) |]
  traverseGlobalRefs resolve (NominalType a0 a1 a2) = [| NominalType (pure a0) (traverseTerms resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (NominalValue a0 a1) = [| NominalValue (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (NominalCase a0 a1 a2) = [| NominalCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (VariantType a0) = [| VariantType (traverseArms resolve a0) |]
  traverseGlobalRefs resolve (VariantValue ty tag Nothing) = (\next => VariantValue next tag Nothing) <$> traverseGlobalRefs resolve ty
  traverseGlobalRefs resolve (VariantValue ty tag (Just value)) = (\next, body => VariantValue next tag (Just body)) <$> traverseGlobalRefs resolve ty <*> traverseGlobalRefs resolve value
  traverseGlobalRefs resolve (DataType a0) = [| DataType (pure a0) |]
  traverseGlobalRefs resolve (DataCon a0 a1 a2) = [| DataCon (pure a0) (pure a1) (pure a2) |]
  traverseGlobalRefs resolve (DataCase a0 a1 a2 a3) = [| DataCase (pure a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseTerms resolve a3) |]
  traverseGlobalRefs resolve (VariantCase a0 a1 a2) = [| VariantCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseTerms resolve a2) |]
  traverseGlobalRefs resolve (BoxType a0 a1) = [| BoxType (pure a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (BoxValue a0 a1) = [| BoxValue (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (BoxCase a0 a1 a2) = [| BoxCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (IOType a0) = [| IOType (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (FileHandleType a0) = [| FileHandleType (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (FileHandleValue a0 a1) = [| FileHandleValue (pure a0) (pure a1) |]
  traverseGlobalRefs resolve (ReadInputFile a0) = [| ReadInputFile (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (WithInputFile a0 a1 a2) = [| WithInputFile (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (IOPure a0) = [| IOPure (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (IOBind a0 a1 a2 a3) = [| IOBind (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (WriteLine a0) = [| WriteLine (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve ReadLine = pure ReadLine
  traverseGlobalRefs resolve (ReadBytes a0) = [| ReadBytes (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve (WriteBytes a0) = [| WriteBytes (traverseGlobalRefs resolve a0) |]
  traverseGlobalRefs resolve FlushBytes = pure FlushBytes
  traverseGlobalRefs resolve (IterateBinary a0 a1 a2 a3 a4) = [| IterateBinary (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) (traverseGlobalRefs resolve a4) |]
  traverseGlobalRefs resolve RejectBytes = pure RejectBytes
  traverseGlobalRefs resolve (BoolCase a0 a1 a2) = [| BoolCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (Sigma a0 a1 a2 a3) = [| Sigma (pure a0) (pure a1) (traverseGlobalRefs resolve a2) (traverseGlobalRefs resolve a3) |]
  traverseGlobalRefs resolve (PairValue a0 a1 a2) = [| PairValue (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (PairCase a0 a1 a2) = [| PairCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (Pi a0 a1 a2) = [| Pi (pure a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (Lambda a0 a1 a2) = [| Lambda (pure a0) (traverseGlobalRefs resolve a1) (traverseGlobalRefs resolve a2) |]
  traverseGlobalRefs resolve (Apply a0 a1) = [| Apply (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (Fix a0 a1) = [| Fix (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]
  traverseGlobalRefs resolve (UnitCase a0 a1) = [| UnitCase (traverseGlobalRefs resolve a0) (traverseGlobalRefs resolve a1) |]

  traverseTerms : Applicative f => (Nat -> f (Term 0)) -> List (Term n) -> f (List (Term n))
  traverseTerms resolve [] = pure []
  traverseTerms resolve (term :: rest) = [| (traverseGlobalRefs resolve term) :: (traverseTerms resolve rest) |]

  traverseArms : Applicative f => (Nat -> f (Term 0)) -> List (Maybe (Quantity, Term n)) -> f (List (Maybe (Quantity, Term n)))
  traverseArms resolve [] = pure []
  traverseArms resolve (Nothing :: rest) = (Nothing ::) <$> traverseArms resolve rest
  traverseArms resolve (Just (q, ty) :: rest) =
    (\a, arms => Just (q, a) :: arms) <$> traverseGlobalRefs resolve ty <*> traverseArms resolve rest

record References a where
  constructor Found
  keys : List Nat

Functor References where
  map f (Found keys) = Found keys

Applicative References where
  pure _ = Found []
  Found left <*> Found right = Found (left ++ right)

||| Includes references in erased types, annotations, dead branches and payloads.
public export
globalReferences : Term n -> List Nat
globalReferences term = keys (traverseGlobalRefs (\key => Found [key]) term)
