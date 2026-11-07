-- Structural size and explicit nominal occurrence inspection, not typing evidence.
module Fibril.Core.Size

import Fibril.Core.Term
import Fibril.Core.Quantity

%default total

mutual
  ||| Exact raw tree size; includes every descriptor/index/branch list cell.
  ||| This is a structural counter, not an allocation/time bound.
  public export
  coreNodes : Term n -> Nat
  coreNodes (Variable _) = 1
  coreNodes (Universe _) = 1
  coreNodes UnitType = 1
  coreNodes UnitValue = 1
  coreNodes BoolType = 1
  coreNodes BoolTrue = 1
  coreNodes BoolFalse = 1
  coreNodes NatType = 1
  coreNodes NatZero = 1
  coreNodes (NatSucc x) = 1 + coreNodes x
  coreNodes (NatRec p z s x) = 1 + coreNodes p + coreNodes z + coreNodes s + coreNodes x
  coreNodes (NatRecRuntime p z s x) = 1 + coreNodes p + coreNodes z + coreNodes s + coreNodes x
  coreNodes (RecType _) = 1
  coreNodes (RecEnd ty) = 1 + coreNodes ty
  coreNodes (RecMore ty x) = 1 + coreNodes ty + coreNodes x
  coreNodes (RecFold p z s x) = 1 + coreNodes p + coreNodes z + coreNodes s + coreNodes x
  coreNodes (RecCase p x z s) = 1 + coreNodes p + coreNodes x + coreNodes z + coreNodes s
  coreNodes (NatCase p x z s) = 1 + coreNodes p + coreNodes x + coreNodes z + coreNodes s
  coreNodes (SeqCase p x z s) = 1 + coreNodes p + coreNodes x + coreNodes z + coreNodes s
  coreNodes (SeqType _ a) = 1 + coreNodes a
  coreNodes (SeqNil ty) = 1 + coreNodes ty
  coreNodes (SeqCons ty h t) = 1 + coreNodes ty + coreNodes h + coreNodes t
  coreNodes (SeqFold p z s x) = 1 + coreNodes p + coreNodes z + coreNodes s + coreNodes x
  coreNodes ReadLine = 1
  coreNodes (FileHandleValue _ _) = 1
  coreNodes (ReadInputFile handle) = 1 + coreNodes handle
  coreNodes StringType = 1
  coreNodes (StringValue _) = 1
  coreNodes (StringAppend a b) = 1 + coreNodes a + coreNodes b
  coreNodes (StringEqual a b) = 1 + coreNodes a + coreNodes b
  coreNodes (NominalType _ indices shape) = 1 + variantTermNodes indices + coreNodes shape
  coreNodes (NominalValue ty value) = 1 + coreNodes ty + coreNodes value
  coreNodes (NominalCase motive value branch) = 1 + coreNodes motive + coreNodes value + coreNodes branch
  coreNodes (VariantType arms) = 1 + variantArmNodes arms
  coreNodes (VariantValue ty _ Nothing) = 1 + coreNodes ty
  coreNodes (VariantValue ty _ (Just value)) = 1 + coreNodes ty + coreNodes value
  coreNodes (VariantCase motive value branches) = 1 + coreNodes motive + coreNodes value + variantTermNodes branches
  coreNodes (BoxType _ a) = 1 + coreNodes a
  coreNodes (BoxValue a b) = 1 + coreNodes a + coreNodes b
  coreNodes (BoxCase a b c) = 1 + coreNodes a + coreNodes b + coreNodes c
  coreNodes (WithInputFile result path body) = 1 + coreNodes result + coreNodes path + coreNodes body
  coreNodes (IOType a) = 1 + coreNodes a
  coreNodes (FileHandleType region) = 1 + coreNodes region
  coreNodes (IOPure a) = 1 + coreNodes a
  coreNodes (WriteLine a) = 1 + coreNodes a
  coreNodes (IOBind a b c d) = 1 + coreNodes a + coreNodes b + coreNodes c + coreNodes d
  coreNodes (BoolCase a b c) = 1 + coreNodes a + coreNodes b + coreNodes c
  coreNodes (Sigma _ _ a b) = 1 + coreNodes a + coreNodes b
  coreNodes (PairCase motive value branch) = 1 + coreNodes motive + coreNodes value + coreNodes branch
  coreNodes (PairValue ty a b) = 1 + coreNodes ty + coreNodes a + coreNodes b
  coreNodes (Pi _ a b) = 1 + coreNodes a + coreNodes b
  coreNodes (Lambda _ a b) = 1 + coreNodes a + coreNodes b
  coreNodes (Fix a b) = 1 + coreNodes a + coreNodes b
  coreNodes (Apply a b) = 1 + coreNodes a + coreNodes b
  coreNodes (UnitCase a b) = 1 + coreNodes a + coreNodes b

  variantArmNodes : List (Maybe (Quantity, Term n)) -> Nat
  variantArmNodes [] = 0
  variantArmNodes (Nothing :: rest) = 1 + variantArmNodes rest
  variantArmNodes (Just (_, ty) :: rest) = 1 + coreNodes ty + variantArmNodes rest

  variantTermNodes : List (Term n) -> Nat
  variantTermNodes [] = 0
  variantTermNodes (x :: xs) = 1 + coreNodes x + variantTermNodes xs



  ||| Find explicit nominal-key occurrences anywhere in expanded syntax.
  ||| Does not resolve globals, inspect variable meanings or establish positivity.
  public export
  mentionsNominal : String -> Term n -> Bool
  mentionsNominal key (Variable _) = False
  mentionsNominal key (Universe _) = False
  mentionsNominal key UnitType = False
  mentionsNominal key UnitValue = False
  mentionsNominal key BoolType = False
  mentionsNominal key BoolTrue = False
  mentionsNominal key BoolFalse = False
  mentionsNominal key NatType = False
  mentionsNominal key NatZero = False
  mentionsNominal key (NatSucc x) = mentionsNominal key x
  mentionsNominal key (NatRec p z s x) = mentionsNominal key p || mentionsNominal key z || mentionsNominal key s || mentionsNominal key x
  mentionsNominal key (NatRecRuntime p z s x) = mentionsNominal key p || mentionsNominal key z || mentionsNominal key s || mentionsNominal key x
  mentionsNominal key (RecType other) = key == other
  mentionsNominal key (RecEnd ty) = mentionsNominal key ty
  mentionsNominal key (RecMore ty x) = mentionsNominal key ty || mentionsNominal key x
  mentionsNominal key (RecFold p z s x) = mentionsNominal key p || mentionsNominal key z || mentionsNominal key s || mentionsNominal key x
  mentionsNominal key (RecCase p x z s) = mentionsNominal key p || mentionsNominal key x || mentionsNominal key z || mentionsNominal key s
  mentionsNominal key (NatCase p x z s) = mentionsNominal key p || mentionsNominal key x || mentionsNominal key z || mentionsNominal key s
  mentionsNominal key (SeqCase p x z s) = mentionsNominal key p || mentionsNominal key x || mentionsNominal key z || mentionsNominal key s
  mentionsNominal key (SeqType other a) = key == other || mentionsNominal key a
  mentionsNominal key (SeqNil ty) = mentionsNominal key ty
  mentionsNominal key (SeqCons ty h t) = mentionsNominal key ty || mentionsNominal key h || mentionsNominal key t
  mentionsNominal key (SeqFold p z s x) = mentionsNominal key p || mentionsNominal key z || mentionsNominal key s || mentionsNominal key x
  mentionsNominal key ReadLine = False
  mentionsNominal key (FileHandleValue _ _) = False
  mentionsNominal key (ReadInputFile handle) = mentionsNominal key handle
  mentionsNominal key StringType = False
  mentionsNominal key (StringValue _) = False
  mentionsNominal key (StringAppend a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (StringEqual a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (NominalType found indices shape) = key == found || anyNominalTerms key indices || mentionsNominal key shape
  mentionsNominal key (NominalValue ty value) = mentionsNominal key ty || mentionsNominal key value
  mentionsNominal key (NominalCase motive value branch) = mentionsNominal key motive || mentionsNominal key value || mentionsNominal key branch
  mentionsNominal key (VariantType arms) = anyNominalArms key arms
  mentionsNominal key (VariantValue ty _ Nothing) = mentionsNominal key ty
  mentionsNominal key (VariantValue ty _ (Just value)) = mentionsNominal key ty || mentionsNominal key value
  mentionsNominal key (VariantCase motive value branches) = mentionsNominal key motive || mentionsNominal key value || anyNominalTerms key branches
  mentionsNominal key (BoxType _ a) = mentionsNominal key a
  mentionsNominal key (BoxValue a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (BoxCase a b c) = mentionsNominal key a || mentionsNominal key b || mentionsNominal key c
  mentionsNominal key (WithInputFile result path body) = mentionsNominal key result || mentionsNominal key path || mentionsNominal key body
  mentionsNominal key (IOType a) = mentionsNominal key a
  mentionsNominal key (FileHandleType region) = mentionsNominal key region
  mentionsNominal key (IOPure a) = mentionsNominal key a
  mentionsNominal key (WriteLine a) = mentionsNominal key a
  mentionsNominal key (IOBind a b c d) = mentionsNominal key a || mentionsNominal key b || mentionsNominal key c || mentionsNominal key d
  mentionsNominal key (BoolCase a b c) = mentionsNominal key a || mentionsNominal key b || mentionsNominal key c
  mentionsNominal key (Sigma _ _ a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (PairCase motive value branch) = mentionsNominal key motive || mentionsNominal key value || mentionsNominal key branch
  mentionsNominal key (PairValue ty a b) = mentionsNominal key ty || mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (Pi _ a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (Lambda _ a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (Fix a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (Apply a b) = mentionsNominal key a || mentionsNominal key b
  mentionsNominal key (UnitCase a b) = mentionsNominal key a || mentionsNominal key b

  anyNominalTerms : String -> List (Term n) -> Bool
  anyNominalTerms key [] = False
  anyNominalTerms key (x :: xs) = mentionsNominal key x || anyNominalTerms key xs

  anyNominalArms : String -> List (Maybe (Quantity, Term n)) -> Bool
  anyNominalArms key [] = False
  anyNominalArms key (Nothing :: xs) = anyNominalArms key xs
  anyNominalArms key (Just (_, ty) :: xs) = mentionsNominal key ty || anyNominalArms key xs
