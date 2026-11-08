-- Conservative whole-syntax runner separation, including erased/dead fields.
module Fibril.Core.EffectAdmission

import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  scan : Bool -> Term n -> Bool
  scan binary (IterateBinary stateType resultType count step initial) = binary || scan binary stateType || scan binary resultType || scan binary count || scan binary step || scan binary initial
  scan binary (ReadBytes x) = binary || scan binary x
  scan binary (WriteBytes x) = binary || scan binary x
  scan binary RejectBytes = binary
  scan binary FlushBytes = binary
  scan binary ReadLine = not binary
  scan binary (WriteLine x) = not binary || scan binary x
  scan binary (WithInputFile a b c) = not binary || scan binary a || scan binary b || scan binary c
  scan binary (ReadInputFile x) = not binary || scan binary x
  scan binary (FileHandleValue _ _) = not binary
  scan binary (FileHandleType x) = not binary || scan binary x
  scan _ (GlobalRef _) = True
  scan _ (Variable _) = False
  scan _ (Universe _) = False
  scan _ UnitType = False
  scan _ UnitValue = False
  scan _ BoolType = False
  scan _ BoolTrue = False
  scan _ BoolFalse = False
  scan _ NatType = False
  scan _ NatZero = False
  scan b (NatSucc x) = scan b x
  scan b (NatRec p z s x) = scan b p || scan b z || scan b s || scan b x
  scan b (NatRecRuntime p z s x) = scan b p || scan b z || scan b s || scan b x
  scan _ (RecType _) = False
  scan b (RecEnd x) = scan b x
  scan b (RecMore a x) = scan b a || scan b x
  scan b (RecFold p z s x) = scan b p || scan b z || scan b s || scan b x
  scan b (RecCase p x z s) = scan b p || scan b x || scan b z || scan b s
  scan b (NatCase p x z s) = scan b p || scan b x || scan b z || scan b s
  scan b (SeqType _ x) = scan b x
  scan b (SeqNil x) = scan b x
  scan b (SeqCons a h t) = scan b a || scan b h || scan b t
  scan b (SeqFold p z s x) = scan b p || scan b z || scan b s || scan b x
  scan b (SeqCase p x z s) = scan b p || scan b x || scan b z || scan b s
  scan _ BytesType = False
  scan _ (BytesValue _) = False
  scan b (BytesAppend x y) = scan b x || scan b y
  scan b (WithRegion x y) = scan b x || scan b y
  scan b (BytesShare x) = scan b x
  scan b (BytesLength x) = scan b x
  scan b (BytesOctet x) = scan b x
  scan b (BytesLengthIs x y) = scan b x || scan b y
  scan b (BytesIndex x y) = scan b x || scan b y
  scan b (BytesSlice x y z) = scan b x || scan b y || scan b z
  scan b (UTF8Encode x) = scan b x
  scan b (UTF8Decode x) = scan b x
  scan _ StringType = False
  scan _ (StringValue _) = False
  scan b (StringAppend x y) = scan b x || scan b y
  scan b (StringEqual x y) = scan b x || scan b y
  scan b (Prim _ args) = scans b args
  scan b (NominalType _ indices shape) = scans b indices || scan b shape
  scan b (NominalValue a x) = scan b a || scan b x
  scan b (NominalCase p x s) = scan b p || scan b x || scan b s
  scan b (VariantType arms) = scanArms b arms
  scan b (VariantValue ty _ Nothing) = scan b ty
  scan b (VariantValue ty _ (Just x)) = scan b ty || scan b x
  scan _ (DataType _) = False
  scan _ (DataCon _ _ _) = False
  scan b (DataCase _ p x branches) = scan b p || scan b x || scans b branches
  scan b (VariantCase p x branches) = scan b p || scan b x || scans b branches
  scan b (BoxType _ x) = scan b x
  scan b (BoxValue a x) = scan b a || scan b x
  scan b (BoxCase p x s) = scan b p || scan b x || scan b s
  scan b (IOType x) = scan b x
  scan b (IOPure x) = scan b x
  scan b (IOBind a c x f) = scan b a || scan b c || scan b x || scan b f
  scan b (BoolCase c x y) = scan b c || scan b x || scan b y
  scan b (Sigma _ _ a c) = scan b a || scan b c
  scan b (PairValue a x y) = scan b a || scan b x || scan b y
  scan b (PairCase p x s) = scan b p || scan b x || scan b s
  scan b (Pi _ a c) = scan b a || scan b c
  scan b (Lambda _ a x) = scan b a || scan b x
  scan b (Fix a x) = scan b a || scan b x
  scan b (Apply f x) = scan b f || scan b x
  scan b (UnitCase x y) = scan b x || scan b y

  scans : Bool -> List (Term n) -> Bool
  scans _ [] = False
  scans b (x :: xs) = scan b x || scans b xs

  scanArms : Bool -> List (Maybe (Quantity, Term n)) -> Bool
  scanArms _ [] = False
  scanArms b (Nothing :: xs) = scanArms b xs
  scanArms b (Just (_, x) :: xs) = scan b x || scanArms b xs

public export
containsBinaryRequest : Term n -> Bool
containsBinaryRequest = scan True

public export
containsNonBinaryIO : Term n -> Bool
containsNonBinaryIO = scan False
