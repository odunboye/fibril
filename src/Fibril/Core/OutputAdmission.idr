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
supportedPrimitive BytesWordAtOp = True
supportedPrimitive NetStreamTypeOp = False
supportedPrimitive NetListenerTypeOp = False
supportedPrimitive NetConnectOp = False
supportedPrimitive NetListenOp = False
supportedPrimitive NetAcceptOp = False
supportedPrimitive NetReadOp = False
supportedPrimitive NetWriteOp = False
supportedPrimitive NetCloseOp = False
supportedPrimitive NetCloseListenerOp = False
supportedPrimitive NetLocalPortOp = False
supportedPrimitive NetShutdownWriteOp = False

mutual
  public export
  admitted : Bool -> Bool -> Term n -> Bool
  admitted net regions (Variable a0) = True
  admitted net regions (GlobalRef a0) = False
  admitted net regions (Universe a0) = True
  admitted net regions UnitType = True
  admitted net regions UnitValue = True
  admitted net regions BoolType = True
  admitted net regions BoolTrue = True
  admitted net regions BoolFalse = True
  admitted net regions NatType = True
  admitted net regions NatZero = True
  admitted net regions (NatSucc a0) = admitted net regions a0
  admitted net regions (NatRec a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (NatRecRuntime a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (RecType a0) = True
  admitted net regions (RecEnd a0) = admitted net regions a0
  admitted net regions (RecMore a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (RecFold a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (RecCase a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (NatCase a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (SeqType a0 a1) = admitted net regions a1
  admitted net regions (SeqNil a0) = admitted net regions a0
  admitted net regions (SeqCons a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (SeqFold a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (SeqCase a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (UTF8Encode a0) = admitted net regions a0
  admitted net regions (UTF8Decode a0) = admitted net regions a0
  admitted net regions BytesType = True
  admitted net regions (BytesValue a0) = True
  admitted net regions (BytesAppend a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (WithRegion a0 a1) = regions && admitted net regions a0 && admitted net regions a1
  admitted net regions (BytesShare a0) = admitted net regions a0
  admitted net regions (BytesLength a0) = admitted net regions a0
  admitted net regions (BytesLengthIs a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (BytesIndex a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (BytesSlice a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (BytesOctet a0) = admitted net regions a0
  admitted net regions StringType = True
  admitted net regions (StringValue a0) = True
  admitted net regions (StringAppend a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (StringEqual a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (Prim a0 a1) = (supportedPrimitive a0 || (net && networkPrimitive a0)) && outputTerms net regions a1
  admitted net regions (NominalType a0 a1 a2) = admitted net regions a2 && outputTerms net regions a1
  admitted net regions (NominalValue a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (NominalCase a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (VariantType a0) = outputArms net regions a0
  admitted net regions (VariantValue ty tag Nothing) = admitted net regions ty
  admitted net regions (VariantValue ty tag (Just value)) = admitted net regions ty && admitted net regions value
  admitted net regions (DataType a0) = True
  admitted net regions (DataCon a0 a1 a2) = True
  admitted net regions (DataCase a0 a1 a2 a3) = admitted net regions a1 && admitted net regions a2 && outputTerms net regions a3
  admitted net regions (VariantCase a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && outputTerms net regions a2
  admitted net regions (BoxType a0 a1) = admitted net regions a1
  admitted net regions (BoxValue a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (BoxCase a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (IOType a0) = admitted net regions a0
  admitted net regions (FileHandleType a0) = False
  admitted net regions (FileHandleValue a0 a1) = False
  admitted net regions (ReadInputFile a0) = False
  admitted net regions (WithInputFile a0 a1 a2) = False
  admitted net regions (IOPure a0) = admitted net regions a0
  admitted net regions (IOBind a0 a1 a2 a3) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2 && admitted net regions a3
  admitted net regions (WriteLine a0) = admitted net regions a0
  admitted net regions ReadLine = False
  admitted net regions (ReadBytes a0) = False
  admitted net regions (WriteBytes a0) = False
  admitted net regions FlushBytes = False
  admitted net regions (IterateBinary a0 a1 a2 a3 a4) = False
  admitted net regions RejectBytes = False
  admitted net regions (BoolCase a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (Sigma a0 a1 a2 a3) = admitted net regions a2 && admitted net regions a3
  admitted net regions (PairValue a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (PairCase a0 a1 a2) = admitted net regions a0 && admitted net regions a1 && admitted net regions a2
  admitted net regions (Pi a0 a1 a2) = admitted net regions a1 && admitted net regions a2
  admitted net regions (Lambda a0 a1 a2) = admitted net regions a1 && admitted net regions a2
  admitted net regions (Apply a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (Fix a0 a1) = admitted net regions a0 && admitted net regions a1
  admitted net regions (UnitCase a0 a1) = admitted net regions a0 && admitted net regions a1

  outputTerms : Bool -> Bool -> List (Term n) -> Bool
  outputTerms net regions [] = True
  outputTerms net regions (term :: rest) = admitted net regions term && outputTerms net regions rest

  outputArms : Bool -> Bool -> List (Maybe (Quantity, Term n)) -> Bool
  outputArms net regions [] = True
  outputArms net regions (Nothing :: rest) = outputArms net regions rest
  outputArms net regions (Just (_, ty) :: rest) = admitted net regions ty && outputArms net regions rest

public export
outputOnly : Bool -> Term n -> Bool
outputOnly = admitted False

public export
networkOnly : Term n -> Bool
networkOnly = admitted True True
