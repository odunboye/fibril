-- Capture-avoiding exact-occurrence abstraction for untrusted motive proposals.
module Fibril.Elaboration.Expression.Abstract

import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  abstractWith : (Fin n -> Fin m) -> Fin m -> Term n -> Term n -> Term m
  abstractWith env hole target term =
    if sameSyntax target term then Variable hole else descend env hole target term

  descend : (Fin n -> Fin m) -> Fin m -> Term n -> Term n -> Term m
  descend env hole target (Variable i) = Variable (env i)
  descend env hole target (Universe l) = Universe l
  descend env hole target UnitType = UnitType
  descend env hole target UnitValue = UnitValue
  descend env hole target BoolType = BoolType
  descend env hole target BoolTrue = BoolTrue
  descend env hole target BoolFalse = BoolFalse
  descend env hole target NatType = NatType
  descend env hole target NatZero = NatZero
  descend env hole target (NatSucc x) = NatSucc (abstractWith env hole target x)
  descend env hole target (NatRec p z s x) = NatRec (abstractWith env hole target p) (abstractWith env hole target z) (abstractWith env hole target s) (abstractWith env hole target x)
  descend env hole target (NatRecRuntime p z s x) = NatRecRuntime (abstractWith env hole target p) (abstractWith env hole target z) (abstractWith env hole target s) (abstractWith env hole target x)
  descend env hole target (RecType key) = RecType key
  descend env hole target (RecEnd ty) = RecEnd (abstractWith env hole target ty)
  descend env hole target (RecMore ty x) = RecMore (abstractWith env hole target ty) (abstractWith env hole target x)
  descend env hole target (RecFold p z s x) = RecFold (abstractWith env hole target p) (abstractWith env hole target z) (abstractWith env hole target s) (abstractWith env hole target x)
  descend env hole target (RecCase p x z s) = RecCase (abstractWith env hole target p) (abstractWith env hole target x) (abstractWith env hole target z) (abstractWith env hole target s)
  descend env hole target (SeqCase p x z s) = SeqCase (abstractWith env hole target p) (abstractWith env hole target x) (abstractWith env hole target z) (abstractWith env hole target s)
  descend env hole target (SeqType key a) = SeqType key (abstractWith env hole target a)
  descend env hole target (SeqNil ty) = SeqNil (abstractWith env hole target ty)
  descend env hole target (SeqCons ty h t) = SeqCons (abstractWith env hole target ty) (abstractWith env hole target h) (abstractWith env hole target t)
  descend env hole target (SeqFold p z s x) = SeqFold (abstractWith env hole target p) (abstractWith env hole target z) (abstractWith env hole target s) (abstractWith env hole target x)
  descend env hole target (ReadBytes x) = ReadBytes (abstractWith env hole target x)
  descend env hole target (WriteBytes x) = WriteBytes (abstractWith env hole target x)
  descend env hole target RejectBytes = RejectBytes
  descend env hole target FlushBytes = FlushBytes
  descend env hole target ReadLine = ReadLine
  descend env hole target (FileHandleValue identity generation) = FileHandleValue identity generation
  descend env hole target (ReadInputFile handle) = ReadInputFile (abstractWith env hole target handle)
  descend env hole target (BytesLengthIs a b) = BytesLengthIs (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (BytesIndex a b) = BytesIndex (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (BytesSlice a b c) = BytesSlice (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c)
  descend env hole target (UTF8Encode x) = UTF8Encode (abstractWith env hole target x)
  descend env hole target (UTF8Decode x) = UTF8Decode (abstractWith env hole target x)
  descend env hole target BytesType = BytesType
  descend env hole target (BytesValue value) = BytesValue value
  descend env hole target (BytesShare x) = BytesShare (abstractWith env hole target x)
  descend env hole target (BytesLength x) = BytesLength (abstractWith env hole target x)
  descend env hole target (BytesOctet x) = BytesOctet (abstractWith env hole target x)
  descend env hole target (BytesAppend a b) = BytesAppend (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target StringType = StringType
  descend env hole target (StringValue value) = StringValue value
  descend env hole target (StringAppend a b) = StringAppend (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (StringEqual a b) = StringEqual (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (NominalType key indices shape) = NominalType key (abstractTerms env hole target indices) (abstractWith env hole target shape)
  descend env hole target (NominalValue a b) = NominalValue (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (NominalCase a b c) = NominalCase (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c)
  descend env hole target (VariantType arms) = VariantType (abstractArms env hole target arms)
  descend env hole target (VariantValue ty tag Nothing) = VariantValue (abstractWith env hole target ty) tag Nothing
  descend env hole target (VariantValue ty tag (Just value)) = VariantValue (abstractWith env hole target ty) tag (Just (abstractWith env hole target value))
  descend env hole target (VariantCase a b branches) = VariantCase (abstractWith env hole target a) (abstractWith env hole target b) (abstractTerms env hole target branches)
  descend env hole target (BoxType q ty) = BoxType q (abstractWith env hole target ty)
  descend env hole target (BoxValue a b) = BoxValue (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (BoxCase a b c) = BoxCase (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c)
  descend env hole target (WithInputFile result path body) = WithInputFile (abstractWith env hole target result) (abstractWith env hole target path) (abstractWith env hole target body)
  descend env hole target (IOType a) = IOType (abstractWith env hole target a)
  descend env hole target (FileHandleType region) = FileHandleType (abstractWith env hole target region)
  descend env hole target (IOPure a) = IOPure (abstractWith env hole target a)
  descend env hole target (WriteLine a) = WriteLine (abstractWith env hole target a)
  descend env hole target (IOBind a b c d) = IOBind (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c) (abstractWith env hole target d)
  descend env hole target (BoolCase a b c) = BoolCase (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c)
  descend env hole target (Sigma q r a b) = Sigma q r (abstractWith env hole target a) (abstractWith (liftRenaming env) (FS hole) (weaken target) b)
  descend env hole target (PairValue a b c) = PairValue (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c)
  descend env hole target (PairCase a b c) = PairCase (abstractWith env hole target a) (abstractWith env hole target b) (abstractWith env hole target c)
  descend env hole target (Pi q a b) = Pi q (abstractWith env hole target a) (abstractWith (liftRenaming env) (FS hole) (weaken target) b)
  descend env hole target (Lambda q a b) = Lambda q (abstractWith env hole target a) (abstractWith (liftRenaming env) (FS hole) (weaken target) b)
  descend env hole target (Apply a b) = Apply (abstractWith env hole target a) (abstractWith env hole target b)
  descend env hole target (UnitCase a b) = UnitCase (abstractWith env hole target a) (abstractWith env hole target b)

  abstractTerms : (Fin n -> Fin m) -> Fin m -> Term n -> List (Term n) -> List (Term m)
  abstractTerms env hole target [] = []
  abstractTerms env hole target (x :: xs) = abstractWith env hole target x :: abstractTerms env hole target xs

  abstractArms : (Fin n -> Fin m) -> Fin m -> Term n -> List (Maybe (Quantity, Term n)) -> List (Maybe (Quantity, Term m))
  abstractArms env hole target [] = []
  abstractArms env hole target (Nothing :: xs) = Nothing :: abstractArms env hole target xs
  abstractArms env hole target (Just (q, ty) :: xs) = Just (q, abstractWith env hole target ty) :: abstractArms env hole target xs

||| Replace exact occurrences of a scoped term with a fresh outer binder.
||| Candidate construction only: callers must bound inputs and check the result.
public export
abstractOver : Term n -> Term n -> Term (S n)
abstractOver target result = abstractWith FS FZ target result
