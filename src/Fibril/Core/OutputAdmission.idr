-- Whole original-syntax capability gate; type/usage/termination checks are separate.
module Fibril.Core.OutputAdmission

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
  outputOnly : Bool -> Term n -> Bool
  outputOnly regions (Variable a0) = True
  outputOnly regions (GlobalRef a0) = False
  outputOnly regions (Universe a0) = True
  outputOnly regions UnitType = True
  outputOnly regions UnitValue = True
  outputOnly regions BoolType = True
  outputOnly regions BoolTrue = True
  outputOnly regions BoolFalse = True
  outputOnly regions NatType = True
  outputOnly regions NatZero = True
  outputOnly regions (NatSucc a0) = outputOnly regions a0
  outputOnly regions (NatRec a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (NatRecRuntime a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (RecType a0) = True
  outputOnly regions (RecEnd a0) = outputOnly regions a0
  outputOnly regions (RecMore a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (RecFold a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (RecCase a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (NatCase a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (SeqType a0 a1) = outputOnly regions a1
  outputOnly regions (SeqNil a0) = outputOnly regions a0
  outputOnly regions (SeqCons a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (SeqFold a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (SeqCase a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (UTF8Encode a0) = outputOnly regions a0
  outputOnly regions (UTF8Decode a0) = outputOnly regions a0
  outputOnly regions BytesType = True
  outputOnly regions (BytesValue a0) = True
  outputOnly regions (BytesAppend a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (WithRegion a0 a1) = regions && outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (BytesShare a0) = outputOnly regions a0
  outputOnly regions (BytesLength a0) = outputOnly regions a0
  outputOnly regions (BytesLengthIs a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (BytesIndex a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (BytesSlice a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (BytesOctet a0) = outputOnly regions a0
  outputOnly regions StringType = True
  outputOnly regions (StringValue a0) = True
  outputOnly regions (StringAppend a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (StringEqual a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (Prim a0 a1) = supportedPrimitive a0 && outputTerms regions a1
  outputOnly regions (NominalType a0 a1 a2) = outputOnly regions a2 && outputTerms regions a1
  outputOnly regions (NominalValue a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (NominalCase a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (VariantType a0) = outputArms regions a0
  outputOnly regions (VariantValue ty tag Nothing) = outputOnly regions ty
  outputOnly regions (VariantValue ty tag (Just value)) = outputOnly regions ty && outputOnly regions value
  outputOnly regions (DataType a0) = True
  outputOnly regions (DataCon a0 a1 a2) = True
  outputOnly regions (DataCase a0 a1 a2 a3) = outputOnly regions a1 && outputOnly regions a2 && outputTerms regions a3
  outputOnly regions (VariantCase a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputTerms regions a2
  outputOnly regions (BoxType a0 a1) = outputOnly regions a1
  outputOnly regions (BoxValue a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (BoxCase a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (IOType a0) = outputOnly regions a0
  outputOnly regions (FileHandleType a0) = False
  outputOnly regions (FileHandleValue a0 a1) = False
  outputOnly regions (ReadInputFile a0) = False
  outputOnly regions (WithInputFile a0 a1 a2) = False
  outputOnly regions (IOPure a0) = outputOnly regions a0
  outputOnly regions (IOBind a0 a1 a2 a3) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (WriteLine a0) = outputOnly regions a0
  outputOnly regions ReadLine = False
  outputOnly regions (ReadBytes a0) = False
  outputOnly regions (WriteBytes a0) = False
  outputOnly regions FlushBytes = False
  outputOnly regions (IterateBinary a0 a1 a2 a3 a4) = False
  outputOnly regions RejectBytes = False
  outputOnly regions (BoolCase a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (Sigma a0 a1 a2 a3) = outputOnly regions a2 && outputOnly regions a3
  outputOnly regions (PairValue a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (PairCase a0 a1 a2) = outputOnly regions a0 && outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (Pi a0 a1 a2) = outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (Lambda a0 a1 a2) = outputOnly regions a1 && outputOnly regions a2
  outputOnly regions (Apply a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (Fix a0 a1) = outputOnly regions a0 && outputOnly regions a1
  outputOnly regions (UnitCase a0 a1) = outputOnly regions a0 && outputOnly regions a1

  outputTerms : Bool -> List (Term n) -> Bool
  outputTerms regions [] = True
  outputTerms regions (term :: rest) = outputOnly regions term && outputTerms regions rest

  outputArms : Bool -> List (Maybe (Quantity, Term n)) -> Bool
  outputArms regions [] = True
  outputArms regions (Nothing :: rest) = outputArms regions rest
  outputArms regions (Just (_, ty) :: rest) = outputOnly regions ty && outputArms regions rest
