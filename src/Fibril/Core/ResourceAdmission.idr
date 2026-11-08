-- Reject runtime references in caller-supplied syntax before resource execution.
module Fibril.Core.ResourceAdmission

import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  public export
  containsFileReference : Term n -> Bool
  containsFileReference (FileHandleValue _ _) = True
  containsFileReference (ReadInputFile handle) = containsFileReference handle
  containsFileReference (GlobalRef _) = True
  containsFileReference (Variable _) = False
  containsFileReference (Universe _) = False
  containsFileReference UnitType = False
  containsFileReference UnitValue = False
  containsFileReference BoolType = False
  containsFileReference BoolTrue = False
  containsFileReference BoolFalse = False
  containsFileReference (IterateBinary stateType resultType count step initial) = containsFileReference stateType || containsFileReference resultType || containsFileReference count || containsFileReference step || containsFileReference initial
  containsFileReference (ReadBytes x) = containsFileReference x
  containsFileReference (WriteBytes x) = containsFileReference x
  containsFileReference RejectBytes = False
  containsFileReference FlushBytes = False
  containsFileReference ReadLine = False
  containsFileReference NatType = False
  containsFileReference NatZero = False
  containsFileReference (NatSucc value) = containsFileReference value
  containsFileReference (NatRec p z s x) = containsFileReference p || containsFileReference z || containsFileReference s || containsFileReference x
  containsFileReference (NatRecRuntime p z s x) = containsFileReference p || containsFileReference z || containsFileReference s || containsFileReference x
  containsFileReference (RecType _) = False
  containsFileReference (RecEnd ty) = containsFileReference ty
  containsFileReference (RecMore ty value) = containsFileReference ty || containsFileReference value
  containsFileReference (RecFold p z s x) = containsFileReference p || containsFileReference z || containsFileReference s || containsFileReference x
  containsFileReference (RecCase p x z s) = containsFileReference p || containsFileReference x || containsFileReference z || containsFileReference s
  containsFileReference (NatCase p x z s) = containsFileReference p || containsFileReference x || containsFileReference z || containsFileReference s
  containsFileReference (SeqType _ element) = containsFileReference element
  containsFileReference (SeqNil ty) = containsFileReference ty
  containsFileReference (SeqCons ty head tail) = containsFileReference ty || containsFileReference head || containsFileReference tail
  containsFileReference (SeqFold p z s x) = containsFileReference p || containsFileReference z || containsFileReference s || containsFileReference x
  containsFileReference (SeqCase p x z s) = containsFileReference p || containsFileReference x || containsFileReference z || containsFileReference s
  containsFileReference (BytesLengthIs a b) = containsFileReference a || containsFileReference b
  containsFileReference (BytesIndex a b) = containsFileReference a || containsFileReference b
  containsFileReference (BytesSlice a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (UTF8Encode x) = containsFileReference x
  containsFileReference (UTF8Decode x) = containsFileReference x
  containsFileReference BytesType = False
  containsFileReference (BytesValue _) = False
  containsFileReference (BytesShare x) = containsFileReference x
  containsFileReference (BytesLength x) = containsFileReference x
  containsFileReference (BytesOctet x) = containsFileReference x
  containsFileReference (BytesAppend a b) = containsFileReference a || containsFileReference b
  containsFileReference (WithRegion a b) = containsFileReference a || containsFileReference b
  containsFileReference StringType = False
  containsFileReference (StringValue _) = False
  containsFileReference (StringAppend a b) = containsFileReference a || containsFileReference b
  containsFileReference (StringEqual a b) = containsFileReference a || containsFileReference b
  containsFileReference (NominalType _ indices shape) = anyReferences indices || containsFileReference shape
  containsFileReference (NominalValue a b) = containsFileReference a || containsFileReference b
  containsFileReference (NominalCase a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (VariantType arms) = armReferences arms
  containsFileReference (VariantValue ty _ Nothing) = containsFileReference ty
  containsFileReference (VariantValue ty _ (Just payload)) = containsFileReference ty || containsFileReference payload
  containsFileReference (DataType _) = False
  containsFileReference (DataCon _ _ _) = False
  containsFileReference (DataCase _ a b branches) = containsFileReference a || containsFileReference b || anyReferences branches
  containsFileReference (VariantCase a b branches) = containsFileReference a || containsFileReference b || anyReferences branches
  containsFileReference (BoxType _ a) = containsFileReference a
  containsFileReference (BoxValue a b) = containsFileReference a || containsFileReference b
  containsFileReference (BoxCase a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (WithInputFile a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (IOType a) = containsFileReference a
  containsFileReference (FileHandleType a) = containsFileReference a
  containsFileReference (IOPure a) = containsFileReference a
  containsFileReference (WriteLine a) = containsFileReference a
  containsFileReference (IOBind a b c d) = containsFileReference a || containsFileReference b || containsFileReference c || containsFileReference d
  containsFileReference (BoolCase a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (Sigma _ _ a b) = containsFileReference a || containsFileReference b
  containsFileReference (PairValue a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (PairCase a b c) = containsFileReference a || containsFileReference b || containsFileReference c
  containsFileReference (Pi _ a b) = containsFileReference a || containsFileReference b
  containsFileReference (Lambda _ a b) = containsFileReference a || containsFileReference b
  containsFileReference (Fix a b) = containsFileReference a || containsFileReference b
  containsFileReference (Apply a b) = containsFileReference a || containsFileReference b
  containsFileReference (UnitCase a b) = containsFileReference a || containsFileReference b

  anyReferences : List (Term n) -> Bool
  anyReferences [] = False
  anyReferences (term :: rest) = containsFileReference term || anyReferences rest

  armReferences : List (Maybe (Quantity, Term n)) -> Bool
  armReferences [] = False
  armReferences (Nothing :: rest) = armReferences rest
  armReferences (Just (_, ty) :: rest) = containsFileReference ty || armReferences rest
