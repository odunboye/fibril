-- Conservative whole-syntax runner separation, including erased/dead fields.
module Fibril.Core.EffectAdmission

import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  scan : Bool -> Bool -> Term n -> Bool
  scan net binary (IterateBinary stateType resultType count step initial) = (not net && binary) || scan net binary stateType || scan net binary resultType || scan net binary count || scan net binary step || scan net binary initial
  scan net binary (ReadBytes x) = (not net && binary) || scan net binary x
  scan net binary (WriteBytes x) = (not net && binary) || scan net binary x
  scan net binary RejectBytes = not net && binary
  scan net binary FlushBytes = not net && binary
  scan net binary ReadLine = not net && not binary
  scan net binary (WriteLine x) = (not net && not binary) || scan net binary x
  scan net binary (WithInputFile a b c) = (not net && not binary) || scan net binary a || scan net binary b || scan net binary c
  scan net binary (ReadInputFile x) = (not net && not binary) || scan net binary x
  scan net binary (FileHandleValue _ _) = not net && not binary
  scan net binary (FileHandleType x) = (not net && not binary) || scan net binary x
  scan net _ (GlobalRef _) = True
  scan net _ (Variable _) = False
  scan net _ (Universe _) = False
  scan net _ UnitType = False
  scan net _ UnitValue = False
  scan net _ BoolType = False
  scan net _ BoolTrue = False
  scan net _ BoolFalse = False
  scan net _ NatType = False
  scan net _ NatZero = False
  scan net b (NatSucc x) = scan net b x
  scan net b (NatRec p z s x) = scan net b p || scan net b z || scan net b s || scan net b x
  scan net b (NatRecRuntime p z s x) = scan net b p || scan net b z || scan net b s || scan net b x
  scan net _ (RecType _) = False
  scan net b (RecEnd x) = scan net b x
  scan net b (RecMore a x) = scan net b a || scan net b x
  scan net b (RecFold p z s x) = scan net b p || scan net b z || scan net b s || scan net b x
  scan net b (RecCase p x z s) = scan net b p || scan net b x || scan net b z || scan net b s
  scan net b (NatCase p x z s) = scan net b p || scan net b x || scan net b z || scan net b s
  scan net b (SeqType _ x) = scan net b x
  scan net b (SeqNil x) = scan net b x
  scan net b (SeqCons a h t) = scan net b a || scan net b h || scan net b t
  scan net b (SeqFold p z s x) = scan net b p || scan net b z || scan net b s || scan net b x
  scan net b (SeqCase p x z s) = scan net b p || scan net b x || scan net b z || scan net b s
  scan net _ BytesType = False
  scan net _ (BytesValue _) = False
  scan net b (BytesAppend x y) = scan net b x || scan net b y
  scan net b (WithRegion x y) = scan net b x || scan net b y
  scan net b (BytesShare x) = scan net b x
  scan net b (BytesLength x) = scan net b x
  scan net b (BytesOctet x) = scan net b x
  scan net b (BytesLengthIs x y) = scan net b x || scan net b y
  scan net b (BytesIndex x y) = scan net b x || scan net b y
  scan net b (BytesSlice x y z) = scan net b x || scan net b y || scan net b z
  scan net b (UTF8Encode x) = scan net b x
  scan net b (UTF8Decode x) = scan net b x
  scan net _ StringType = False
  scan net _ (StringValue _) = False
  scan net b (StringAppend x y) = scan net b x || scan net b y
  scan net b (StringEqual x y) = scan net b x || scan net b y
  scan net b (Prim op args) = (net && networkPrimitive op) || scans net b args
  scan net b (NominalType _ indices shape) = scans net b indices || scan net b shape
  scan net b (NominalValue a x) = scan net b a || scan net b x
  scan net b (NominalCase p x s) = scan net b p || scan net b x || scan net b s
  scan net b (VariantType arms) = scanArms net b arms
  scan net b (VariantValue ty _ Nothing) = scan net b ty
  scan net b (VariantValue ty _ (Just x)) = scan net b ty || scan net b x
  scan net _ (DataType _) = False
  scan net _ (DataCon _ _ _) = False
  scan net b (DataCase _ p x branches) = scan net b p || scan net b x || scans net b branches
  scan net b (VariantCase p x branches) = scan net b p || scan net b x || scans net b branches
  scan net b (BoxType _ x) = scan net b x
  scan net b (BoxValue a x) = scan net b a || scan net b x
  scan net b (BoxCase p x s) = scan net b p || scan net b x || scan net b s
  scan net b (IOType x) = scan net b x
  scan net b (IOPure x) = scan net b x
  scan net b (IOBind a c x f) = scan net b a || scan net b c || scan net b x || scan net b f
  scan net b (BoolCase c x y) = scan net b c || scan net b x || scan net b y
  scan net b (Sigma _ _ a c) = scan net b a || scan net b c
  scan net b (PairValue a x y) = scan net b a || scan net b x || scan net b y
  scan net b (PairCase p x s) = scan net b p || scan net b x || scan net b s
  scan net b (Pi _ a c) = scan net b a || scan net b c
  scan net b (Lambda _ a x) = scan net b a || scan net b x
  scan net b (Fix a x) = scan net b a || scan net b x
  scan net b (Apply f x) = scan net b f || scan net b x
  scan net b (UnitCase x y) = scan net b x || scan net b y

  scans : Bool -> Bool -> List (Term n) -> Bool
  scans net _ [] = False
  scans net b (x :: xs) = scan net b x || scans net b xs

  scanArms : Bool -> Bool -> List (Maybe (Quantity, Term n)) -> Bool
  scanArms net _ [] = False
  scanArms net b (Nothing :: xs) = scanArms net b xs
  scanArms net b (Just (_, x) :: xs) = scan net b x || scanArms net b xs

public export
containsBinaryRequest : Term n -> Bool
containsBinaryRequest term = scan False True term || scan True False term

public export
containsNonBinaryIO : Term n -> Bool
containsNonBinaryIO term = scan False False term || scan True False term

public export
containsNetworkRequest : Term n -> Bool
containsNetworkRequest = scan True False

public export
containsBinaryTransport : Term n -> Bool
containsBinaryTransport = scan False True
