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
  constructor MkConstructor
  name : String
  fields : Telescope width

||| A family: its qualified key, erased parameters and constructors in declaration order.
public export
record DataDecl where
  constructor MkDataDecl
  key : String
  params : Telescope 0
  constructors : List (Constructor (telescopeLength params))

-- Admission caps. They bound the work of later phases (case branches, generated IR); they
-- are not hard resource limits.
public export
maxParameters : Nat
maxParameters = 4

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
describe (Apply _ _) = "a recursive occurrence must be the family applied to exactly its own parameters, in order"
describe _ = "a recursive occurrence must be the whole type of a field"

checkFields : {n : Nat} -> String -> Nat -> String -> Nat -> Telescope n -> Either String ()
checkFields key count ctor position Done = Right ()
checkFields {n} key count ctor position (Field _ ty rest) =
  let mentions = mentionsNominal key ty
      isSelf = case selfType key count n of
        Just expected => sameSyntax ty expected
        Nothing => False
   in if mentions && not isSelf
        then Left ("constructor " ++ ctor ++ ", field " ++ show position ++ ": " ++ describe ty)
        else checkFields key count ctor (S position) rest

checkParameters : String -> Nat -> Telescope n -> Either String ()
checkParameters key position Done = Right ()
checkParameters key position (Field q ty rest) =
  if q /= Erased then Left ("parameter " ++ show position ++ " must be erased")
  else if mentionsNominal key ty then Left ("parameter " ++ show position ++ " may not mention the family")
  else checkParameters key (S position) rest

checkConstructors : {width : Nat} -> String -> List String -> List (Constructor width) -> Either String ()
checkConstructors key seen [] = Right ()
checkConstructors {width} key seen (ctor :: rest) =
  if ctor.name == "" then Left "constructor names must not be empty"
  else if elem ctor.name seen then Left ("duplicate constructor " ++ ctor.name)
  else if telescopeLength ctor.fields > maxFields
    then Left ("constructor " ++ ctor.name ++ " has more than " ++ show maxFields ++ " fields")
  else do
    checkFields key width ctor.name 1 ctor.fields
    checkConstructors key (ctor.name :: seen) rest

||| Admit a declaration only if every recursive occurrence is a whole field type spelling the
||| family applied to its own parameters. This is strict positivity in its narrowest form:
||| nothing nested, indexed, mutual or under a function type is accepted.
public export
admitDeclaration : DataDecl -> Either String ()
admitDeclaration decl =
  let count = telescopeLength decl.params
   in if decl.key == "" then Left "a family needs a key"
      else if count > maxParameters then Left ("more than " ++ show maxParameters ++ " parameters")
      else if length decl.constructors > maxConstructors then Left ("more than " ++ show maxConstructors ++ " constructors")
      else do
        checkParameters decl.key 1 decl.params
        checkConstructors decl.key [] decl.constructors

-- Types of the family and its constructors, as closed terms. ------------------------------

-- Pi over a parameter telescope, then `inner`, which lives under all of its binders.
paramsPi : {n : Nat} -> (ps : Telescope n) -> Term (telescopeLength ps + n) -> Term n
paramsPi Done inner = inner
paramsPi {n} (Field q ty rest) inner =
  Pi q ty (paramsPi rest (replace {p = Term} (plusSuccRightSucc (telescopeLength rest) n) inner))

-- Pi over fields, ending in whatever `result` builds for the innermost scope.
fieldsPi : {w : Nat} -> Telescope w -> ((m : Nat) -> Term m) -> Term w
fieldsPi {w} Done result = result w
fieldsPi (Field q ty rest) result = Pi q ty (fieldsPi rest result)

||| `(0 p1 : P1) -> ... -> Type 0`: the family applied to its parameters is a type.
public export
formerType : DataDecl -> Term 0
formerType decl = paramsPi decl.params (Universe 0)

nthConstructor : Nat -> List a -> Maybe a
nthConstructor _ [] = Nothing
nthConstructor Z (x :: _) = Just x
nthConstructor (S k) (_ :: xs) = nthConstructor k xs

resultAt : String -> Nat -> (m : Nat) -> Term m
resultAt key count m = fromMaybe (DataType key) (selfType key count m)

||| The type of constructor `index`: the parameters (erased), then its fields with their
||| quantities, ending in the family applied to the same parameters.
public export
constructorType : DataDecl -> Nat -> Maybe (Term 0)
constructorType decl index = do
  ctor <- nthConstructor index decl.constructors
  let fieldsTerm = fieldsPi ctor.fields (resultAt decl.key (telescopeLength decl.params))
  Just (paramsPi decl.params (replace {p = Term} (sym (plusZeroRightNeutral (telescopeLength decl.params))) fieldsTerm))

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
