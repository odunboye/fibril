-- Whole original-syntax capability gate; type/usage/termination checks are separate.
module Fibril.Driver.JavaScript.Admission

import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

-- Exhaustive: a future primitive needs an explicit backend admission decision.
supportedPrimitive : PrimOp -> Bool
supportedPrimitive WordTypeOp = True
supportedPrimitive (WordLitOp _) = True
supportedPrimitive WordAddOp = True
supportedPrimitive WordSubOp = True
supportedPrimitive WordMulOp = True
supportedPrimitive WordEqOp = True
supportedPrimitive WordLtOp = True
supportedPrimitive WordToStringOp = True
supportedPrimitive WordDivOp = True
supportedPrimitive WordRemOp = True
supportedPrimitive WordFromNatOp = True
supportedPrimitive BytesEqualOp = True

mutual
  public export
  supported : Term n -> Bool
  supported (Variable a0) = True
  supported (GlobalRef a0) = False
  supported (Universe a0) = True
  supported UnitType = True
  supported UnitValue = True
  supported BoolType = True
  supported BoolTrue = True
  supported BoolFalse = True
  supported NatType = True
  supported NatZero = True
  supported (NatSucc a0) = supported a0
  supported (NatRec a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (NatRecRuntime a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (RecType a0) = True
  supported (RecEnd a0) = supported a0
  supported (RecMore a0 a1) = supported a0 && supported a1
  supported (RecFold a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (RecCase a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (NatCase a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (SeqType a0 a1) = supported a1
  supported (SeqNil a0) = supported a0
  supported (SeqCons a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (SeqFold a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (SeqCase a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (UTF8Encode a0) = supported a0
  supported (UTF8Decode a0) = supported a0
  supported BytesType = True
  supported (BytesValue a0) = True
  supported (BytesAppend a0 a1) = supported a0 && supported a1
  supported (WithRegion a0 a1) = False
  supported (BytesShare a0) = supported a0
  supported (BytesLength a0) = supported a0
  supported (BytesLengthIs a0 a1) = supported a0 && supported a1
  supported (BytesIndex a0 a1) = supported a0 && supported a1
  supported (BytesSlice a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (BytesOctet a0) = supported a0
  supported StringType = True
  supported (StringValue a0) = True
  supported (StringAppend a0 a1) = supported a0 && supported a1
  supported (StringEqual a0 a1) = supported a0 && supported a1
  supported (Prim a0 a1) = supportedPrimitive a0 && supportedTerms a1
  supported (NominalType a0 a1 a2) = supported a2 && supportedTerms a1
  supported (NominalValue a0 a1) = supported a0 && supported a1
  supported (NominalCase a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (VariantType a0) = supportedArms a0
  supported (VariantValue ty tag Nothing) = supported ty
  supported (VariantValue ty tag (Just value)) = supported ty && supported value
  supported (DataType a0) = True
  supported (DataCon a0 a1 a2) = True
  supported (DataCase a0 a1 a2 a3) = supported a1 && supported a2 && supportedTerms a3
  supported (VariantCase a0 a1 a2) = supported a0 && supported a1 && supportedTerms a2
  supported (BoxType a0 a1) = supported a1
  supported (BoxValue a0 a1) = supported a0 && supported a1
  supported (BoxCase a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (IOType a0) = supported a0
  supported (FileHandleType a0) = False
  supported (FileHandleValue a0 a1) = False
  supported (ReadInputFile a0) = False
  supported (WithInputFile a0 a1 a2) = False
  supported (IOPure a0) = supported a0
  supported (IOBind a0 a1 a2 a3) = supported a0 && supported a1 && supported a2 && supported a3
  supported (WriteLine a0) = supported a0
  supported ReadLine = False
  supported (ReadBytes a0) = False
  supported (WriteBytes a0) = False
  supported FlushBytes = False
  supported (IterateBinary a0 a1 a2 a3 a4) = False
  supported RejectBytes = False
  supported (BoolCase a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (Sigma a0 a1 a2 a3) = supported a2 && supported a3
  supported (PairValue a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (PairCase a0 a1 a2) = supported a0 && supported a1 && supported a2
  supported (Pi a0 a1 a2) = supported a1 && supported a2
  supported (Lambda a0 a1 a2) = supported a1 && supported a2
  supported (Apply a0 a1) = supported a0 && supported a1
  supported (Fix a0 a1) = supported a0 && supported a1
  supported (UnitCase a0 a1) = supported a0 && supported a1

  supportedTerms : List (Term n) -> Bool
  supportedTerms [] = True
  supportedTerms (term :: rest) = supported term && supportedTerms rest

  supportedArms : List (Maybe (Quantity, Term n)) -> Bool
  supportedArms [] = True
  supportedArms (Nothing :: rest) = supportedArms rest
  supportedArms (Just (_, ty) :: rest) = supported ty && supportedArms rest
