-- Declarations of general recursive data, and the admission rule that keeps them positive.
-- Phase 2 of docs/general-recursive-data-plan.md: this module decides which declarations
-- are admissible. It does not type constructors or eliminators (phase 3) and is not a
-- soundness proof.
module Fibril.Core.DataDecl

import Data.Fin
import Data.List
import Data.Maybe
import Data.Nat
import Fibril.Core.Quantity
import Fibril.Core.Size
import Fibril.Core.Term

%default total

||| A telescope of fields in scope `n`: each field's type may mention the parameters and
||| the fields before it, which is why the scope grows by one per field.
public export
data Telescope : Nat -> Type where
  Done : Telescope n
  Field : Quantity -> Term n -> Telescope (S n) -> Telescope n

public export
telescopeLength : Telescope n -> Nat
telescopeLength Done = 0
telescopeLength (Field _ _ rest) = S (telescopeLength rest)

||| One constructor. `width` is the number of parameters in scope.
public export
record Constructor (width : Nat) where
  constructor IndexedConstructor
  name : String
  fields : Telescope width
  resultIndices : List (Term (telescopeLength fields + width))

public export
MkConstructor : String -> Telescope width -> Constructor width
MkConstructor name fields = IndexedConstructor name fields []

||| A family with uniform erased parameters, a dependent erased index telescope,
||| and constructors whose result indices live under their own field telescopes.
public export
record DataDecl where
  constructor IndexedDataDecl
  key : String
  params : Telescope 0
  indices : Telescope (telescopeLength params)
  constructors : List (Constructor (telescopeLength params))

public export
MkDataDecl : String -> (params : Telescope 0) -> List (Constructor (telescopeLength params)) -> DataDecl
MkDataDecl key params constructors = IndexedDataDecl key params Done constructors

-- Admission caps. They bound the work of later phases (case branches, generated IR); they
-- are not hard resource limits.
public export
maxParameters : Nat
maxParameters = 4

public export
maxIndices : Nat
maxIndices = 4

public export
maxConstructors : Nat
maxConstructors = 16

public export
maxFields : Nat
maxFields = 8

-- The recursive occurrence as a field must spell: the family applied to its own parameters,
-- unchanged and in order. `n` is the scope the field is written in.
public export
selfType : String -> Nat -> (n : Nat) -> Maybe (Term n)
selfType key count n = go 0 count (DataType key)
  where
    go : Nat -> Nat -> Term n -> Maybe (Term n)
    go _ Z acc = Just acc
    go j (S remaining) acc = do
      i <- natToFin (minus (minus n 1) j) n
      go (S j) remaining (Apply acc (Variable i))

-- Why a field type that mentions the family is not the plain recursive occurrence.
describe : Term n -> String
describe (Pi _ _ _) = "a recursive occurrence under a function type is not accepted"
describe (Apply _ _) = "a recursive occurrence must use its own parameters unchanged, followed by the declared indices"
describe _ = "a recursive occurrence must be the whole type of a field"

public export
indexCount : DataDecl -> Nat
indexCount decl = telescopeLength decl.indices

applicationSpine : Term n -> (Term n, List (Term n))
applicationSpine term = go term []
  where
    go : Term m -> List (Term m) -> (Term m, List (Term m))
    go (Apply function argument) args = go function (argument :: args)
    go head args = (head, args)

-- Intrinsic fixed sequences are strictly positive in their element type.
-- Unknown user containers and function-space occurrences remain rejected.
positiveField : {n : Nat} -> Nat -> String -> Nat -> Nat -> Term n -> Bool
positiveField Z key count indices ty = False
positiveField (S fuel) key count indices (SeqType _ element) = positiveField fuel key count indices element
positiveField {n} (S fuel) key count indices ty = case applicationSpine ty of
  (DataType other, args) => other == key && length args == count + indices &&
    (case selfType key count n of
      Just expected => sameSyntax (foldl Apply (DataType key) (take count args)) expected
      Nothing => False) && not (any (mentionsNominal key) (drop count args))
  _ => False

checkFields : {n : Nat} -> String -> Nat -> Nat -> String -> Nat -> Telescope n -> Either String ()
checkFields key count indices ctor position Done = Right ()
checkFields {n} key count indices ctor position (Field _ ty rest) =
  let mentions = mentionsNominal key ty
      isSelf = positiveField 64 key count indices ty
   in if mentions && not isSelf
        then Left ("constructor " ++ ctor ++ ", field " ++ show position ++ ": " ++ describe ty)
        else checkFields key count indices ctor (S position) rest

checkParameters : String -> Nat -> Telescope n -> Either String ()
checkParameters key position Done = Right ()
checkParameters key position (Field q ty rest) =
  if q /= Erased then Left ("parameter " ++ show position ++ " must be erased")
  else if mentionsNominal key ty then Left ("parameter " ++ show position ++ " may not mention the family")
  else checkParameters key (S position) rest

checkConstructors : {width : Nat} -> String -> Nat -> List String -> List (Constructor width) -> Either String ()
checkConstructors key indices seen [] = Right ()
checkConstructors {width} key indices seen (ctor :: rest) =
  if ctor.name == "" then Left "constructor names must not be empty"
  else if elem ctor.name seen then Left ("duplicate constructor " ++ ctor.name)
  else if telescopeLength ctor.fields > maxFields
    then Left ("constructor " ++ ctor.name ++ " has more than " ++ show maxFields ++ " fields")
  else do
    if length ctor.resultIndices /= indices then Left ("constructor " ++ ctor.name ++ " has the wrong number of result indices") else Right ()
    if any (mentionsNominal key) ctor.resultIndices then Left "constructor result indices may not mention their own family" else Right ()
    checkFields key width indices ctor.name 1 ctor.fields
    checkConstructors key indices (ctor.name :: seen) rest

||| Every recursive occurrence must be a whole field type with unchanged uniform
||| parameters. Indices may vary, but may not themselves mention this family.
||| Nested, mutual and function-space recursion remain outside this positive slice.
public export
admitDeclaration : DataDecl -> Either String ()
admitDeclaration decl =
  let count = telescopeLength decl.params
   in if decl.key == "" then Left "a family needs a key"
      else if count > maxParameters then Left ("more than " ++ show maxParameters ++ " parameters")
      else if length decl.constructors > maxConstructors then Left ("more than " ++ show maxConstructors ++ " constructors")
      else do
        checkParameters decl.key 1 decl.params
        if indexCount decl > maxIndices then Left "more than 4 indices" else Right ()
        checkParameters decl.key 1 decl.indices
        checkConstructors decl.key (indexCount decl) [] decl.constructors

-- Types of the family and its constructors, as closed terms. ------------------------------

-- Pi over a parameter telescope, then `inner`, which lives under all of its binders.
paramsPi : {n : Nat} -> (ps : Telescope n) -> Term (telescopeLength ps + n) -> Term n
paramsPi Done inner = inner
paramsPi {n} (Field q ty rest) inner =
  Pi q ty (paramsPi rest (replace {p = Term} (plusSuccRightSucc (telescopeLength rest) n) inner))

||| The erased parameter and index telescope, ending in Type 0.
public export
formerType : DataDecl -> Term 0
formerType decl = paramsPi decl.params
  (replace {p = Term} (sym (plusZeroRightNeutral (telescopeLength decl.params)))
    (paramsPi decl.indices (Universe 0)))

nthConstructor : Nat -> List a -> Maybe a
nthConstructor _ [] = Nothing
nthConstructor Z (x :: _) = Just x
nthConstructor (S k) (_ :: xs) = nthConstructor k xs

resultAt : String -> Nat -> (m : Nat) -> Term m
resultAt key count m = fromMaybe (DataType key) (selfType key count m)

||| The type of constructor `index`: the parameters (erased), then its fields with their
||| quantities, ending in the same parameters and this constructor's result indices.
public export
constructorType : DataDecl -> Nat -> Maybe (Term 0)
constructorType decl index = do
  ctor <- nthConstructor index decl.constructors
  let result = foldl Apply
        (resultAt decl.key (telescopeLength decl.params) (telescopeLength ctor.fields + telescopeLength decl.params)) ctor.resultIndices
  let fieldsTerm = paramsPi ctor.fields result
  Just (paramsPi decl.params (replace {p = Term} (sym (plusZeroRightNeutral (telescopeLength decl.params))) fieldsTerm))

-- Lambda over a parameter telescope, then `inner` under all of its binders.
paramsLam : {n : Nat} -> (ps : Telescope n) -> Term (telescopeLength ps + n) -> Term n
paramsLam Done inner = inner
paramsLam {n} (Field q ty rest) inner =
  Lambda q ty (paramsLam rest (replace {p = Term} (plusSuccRightSucc (telescopeLength rest) n) inner))

||| `\(0 p1 : P1) ... => Family p1 ...`: the family as a function of its parameters. This is
||| the value a source declaration gives the family's name.
public export
formerValue : DataDecl -> Term 0
formerValue decl = paramsLam decl.params
  (replace {p = Term} (sym (plusZeroRightNeutral (telescopeLength decl.params)))
    (paramsLam decl.indices (resultAt decl.key (telescopeLength decl.params + indexCount decl)
      (indexCount decl + telescopeLength decl.params))))

||| How many parameters and constructors, for callers that only need the shape.
public export
parameterCount : DataDecl -> Nat
parameterCount decl = telescopeLength decl.params

public export
constructorCount : DataDecl -> Nat
constructorCount decl = length decl.constructors

||| Number of fields of constructor `index`.
public export
fieldCount : DataDecl -> Nat -> Maybe Nat
fieldCount decl index = map (\ctor => telescopeLength ctor.fields) (nthConstructor index decl.constructors)
