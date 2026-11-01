-- Experimental erased ordinary-fragment checker, not the Fibril kernel.
-- Theory: ATKEY18 sec. 2.1.3; details/departures in docs/erased-checker.md.
-- Primitive Unit/Bool rules are local designs; see docs/unit.md, docs/boolean.md.
module Fibril.Core.Erased

import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Compatibility
import Fibril.Core.WeakHead
import Fibril.Core.Reduction

%default total

||| Failures distinguish exhausted checking/reduction from actual rejection.
public export
data CheckError
  = CheckingLimit
  | ReductionLimit
  | ExpectedUniverse
  | ExpectedFunction
  | TypeMismatch
  | BranchTypeMismatch

public export
Show CheckError where
  show CheckingLimit = "Checking recursion budget exhausted"
  show ReductionLimit = "Reduction budget exhausted"
  show ExpectedUniverse = "Expected a universe"
  show ExpectedFunction = "Expected a dependent function type"
  show TypeMismatch = "Inferred type is not compatible with expected type"
  show BranchTypeMismatch = "Conditional branch types are not equal"

-- Inspect only the outer type shape; comparison still uses full normalization.
exposeType : Nat -> Term n -> Either CheckError (Term n)
exposeType budget term =
  case weakHead budget term of
    HeadForm result => Right result
    HeadLimit _ => Left ReductionLimit

requireCompatible : Nat -> Term n -> Term n -> Either CheckError ()
requireCompatible budget actual expected =
  case compatibleTypes budget actual expected of
    Compatible => Right ()
    Incompatible => Left TypeMismatch
    CompatibilityLimit => Left ReductionLimit

-- Internal inference assumes context formation has already been checked.
-- Every recursive typing call decreases depth. Reduction has a separate budget.
mutual
  infer : Nat -> Nat -> Context n -> Term n -> Either CheckError (Term n)
  infer Z reduction context term = Left CheckingLimit
  infer (S depth) reduction context (Variable i) = Right (lookupType i context)
  infer (S depth) reduction context (Universe level) = Right (Universe (S level))
  infer (S depth) reduction context UnitType = Right (Universe 0)
  infer (S depth) reduction context UnitValue = Right UnitType
  infer (S depth) reduction context BoolType = Right (Universe 0)
  infer (S depth) reduction context BoolTrue = Right BoolType
  infer (S depth) reduction context BoolFalse = Right BoolType
  infer (S depth) reduction context (BoolCase condition yes no) = do
    conditionType <- infer depth reduction context condition
    requireCompatible reduction conditionType BoolType
    yesType <- infer depth reduction context yes
    noType <- infer depth reduction context no
    case betaCompare reduction yesType noType of
      EqualNormalForms => Right yesType
      DifferentNormalForms => Left BranchTypeMismatch
      Inconclusive => Left ReductionLimit
  infer (S depth) reduction context (Pi q domain body) = do
    domainLevel <- sortOf depth reduction context domain
    bodyLevel <- sortOf depth reduction (Extend context q domain) body
    Right (Universe (max domainLevel bodyLevel))
  infer (S depth) reduction context (Lambda q domain body) = do
    _ <- sortOf depth reduction context domain
    bodyType <- infer depth reduction (Extend context q domain) body
    Right (Pi q domain bodyType)
  infer (S depth) reduction context (Apply function argument) = do
    functionType <- infer depth reduction context function
    exposed <- exposeType reduction functionType
    case exposed of
      Pi q domain body => do
        argumentType <- infer depth reduction context argument
        requireCompatible reduction argumentType domain
        Right (instantiateTerm argument body)
      _ => Left ExpectedFunction

  infer (S depth) reduction context (UnitCase scrutinee body) = do
    scrutineeType <- infer depth reduction context scrutinee
    requireCompatible reduction scrutineeType UnitType
    infer depth reduction context body

  sortOf : Nat -> Nat -> Context n -> Term n -> Either CheckError Nat
  sortOf depth reduction context term = do
    ty <- infer depth reduction context term
    exposed <- exposeType reduction ty
    case exposed of
      Universe level => Right level
      _ => Left ExpectedUniverse

formation : Nat -> Nat -> Context n -> Either CheckError ()
formation depth reduction Empty = Right ()
formation Z reduction (Extend rest q domain) = Left CheckingLimit
formation (S depth) reduction (Extend rest q domain) = do
  formation depth reduction rest
  _ <- sortOf depth reduction rest domain
  Right ()

||| Check that each stored context domain is a type in its preceding context.
||| This erased judgment imposes no runtime coefficient obligations.
public export
checkErasedContext : (depth : Nat) -> (reduction : Nat) -> Context n -> Either CheckError ()
checkErasedContext = formation

||| Infer an ordinary term's type after validating its context.
||| This is erased-only: success does not authorize runtime resource use.
public export
inferErased : (depth : Nat) -> (reduction : Nat) -> Context n -> Term n ->
              Either CheckError (Term n)
inferErased depth reduction context term = do
  formation depth reduction context
  infer depth reduction context term

||| Validate expected type formation, infer the term, then check compatibility.
||| Literal universes lift upwards; Pi/quantity structure remains invariant.
public export
checkErased : (depth : Nat) -> (reduction : Nat) -> Context n ->
              (term : Term n) -> (expected : Term n) -> Either CheckError ()
checkErased depth reduction context term expected = do
  formation depth reduction context
  _ <- sortOf depth reduction context expected
  actual <- infer depth reduction context term
  requireCompatible reduction actual expected
