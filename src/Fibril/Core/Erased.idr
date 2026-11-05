-- Experimental erased ordinary-fragment checker, not the Fibril kernel.
-- Theory: ATKEY18 sec. 2.1.3; details/departures in docs/erased-checker.md.
-- Primitive Unit/Bool rules are local designs; see docs/unit.md, docs/boolean.md.
module Fibril.Core.Erased

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Context
import Fibril.Core.Compatibility
import Fibril.Core.WeakHead
import Fibril.Core.Reduction

%default total

||| Failures distinguish exhausted checking/reduction from actual rejection.
public export
data CheckError : Type where
  NatError : String -> CheckError
  NominalError : String -> CheckError
  VariantError : String -> CheckError
  CheckingLimit : CheckError
  ReductionLimit : CheckError
  ExpectedUniverse : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedPairMotive : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedBoxMotive : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedBoxType : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedPairType : {0 n : Nat} -> (found : Term n) -> CheckError
  ExpectedFunction : {0 n : Nat} -> (found : Term n) -> CheckError
  ||| Both types retain a shared scope; payloads are diagnostic data, not proofs.
  TypeMismatch : {0 n : Nat} -> (actual, expected : Term n) -> CheckError
  BranchTypeMismatch : {0 n : Nat} -> (yesType, noType : Term n) -> CheckError

public export
Show CheckError where
  show (NatError message) = "Nat: " ++ message
  show (NominalError message) = "Nominal: " ++ message
  show (VariantError message) = "Variant: " ++ message
  show CheckingLimit = "Checking recursion budget exhausted"
  show ReductionLimit = "Reduction budget exhausted"
  show (ExpectedUniverse found) = "Expected a universe; found: " ++ renderTerm found
  show (ExpectedPairMotive found) = "Expected an erased pair motive returning a universe; found: " ++ renderTerm found
  show (ExpectedPairType found) = "Expected a dependent pair type; found: " ++ renderTerm found
  show (ExpectedBoxMotive found) = "Expected an erased box motive returning a universe; found: " ++ renderTerm found
  show (ExpectedBoxType found) = "Expected a unary box type; found: " ++ renderTerm found
  show (ExpectedFunction found) = "Expected a dependent function type; found: " ++ renderTerm found
  show (TypeMismatch actual expected) =
    "Inferred type is not compatible with expected type; inferred: " ++ renderTerm actual ++
    "; expected: " ++ renderTerm expected
  show (BranchTypeMismatch yesType noType) =
    "Conditional branch types are not equal; then: " ++ renderTerm yesType ++
    "; else: " ++ renderTerm noType

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
    Incompatible => Left (TypeMismatch actual expected)
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
  infer (S depth) reduction context NatType = Right (Universe 0)
  infer (S depth) reduction context NatZero = Right NatType
  infer (S depth) reduction context (NatSucc value) = do
    ty <- infer depth reduction context value
    requireCompatible reduction ty NatType
    Right NatType
  infer (S depth) reduction context (NatRec motive base next value) = do
    valueType <- infer depth reduction context value
    requireCompatible reduction valueType NatType
    motiveType <- infer depth reduction context motive
    motiveHead <- exposeType reduction motiveType
    case motiveHead of
      Pi Erased parameter result => do
        requireCompatible reduction parameter NatType
        resultHead <- exposeType reduction result
        case resultHead of
          Universe _ => Right ()
          _ => Left (ExpectedUniverse resultHead)
      _ => Left (NatError "recursor motive must have an erased Nat binder and return a universe")
    baseType <- infer depth reduction context base
    requireCompatible reduction baseType (Apply motive NatZero)
    nextType <- infer depth reduction context next
    let ihType = Apply (weaken motive) (Variable FZ)
    let resultType = Apply (weaken (weaken motive)) (NatSucc (Variable (FS FZ)))
    requireCompatible reduction nextType (Pi Erased NatType (Pi Linear ihType resultType))
    Right (Apply motive value)
  infer (S depth) reduction context (NatRecRuntime motive base next value) = do
    valueType <- infer depth reduction context value
    requireCompatible reduction valueType NatType
    motiveType <- infer depth reduction context motive
    motiveHead <- exposeType reduction motiveType
    case motiveHead of
      Pi Erased parameter result => do
        requireCompatible reduction parameter NatType
        resultHead <- exposeType reduction result
        case resultHead of
          Universe _ => Right ()
          _ => Left (ExpectedUniverse resultHead)
      _ => Left (NatError "recursor motive must have an erased Nat binder and return a universe")
    baseType <- infer depth reduction context base
    requireCompatible reduction baseType (Apply motive NatZero)
    nextType <- infer depth reduction context next
    let ihType = Apply (weaken motive) (Variable FZ)
    let resultType = Apply (weaken (weaken motive)) (NatSucc (Variable (FS FZ)))
    requireCompatible reduction nextType (Pi Unrestricted NatType (Pi Linear ihType resultType))
    Right (Apply motive value)
  infer (S depth) reduction context StringType = Right (Universe 0)
  infer (S depth) reduction context (StringValue _) = Right StringType
  infer (S depth) reduction context (StringAppend left right) = do
    leftType <- infer depth reduction context left
    requireCompatible reduction leftType StringType
    rightType <- infer depth reduction context right
    requireCompatible reduction rightType StringType
    Right StringType
  infer (S depth) reduction context (StringEqual left right) = do
    leftType <- infer depth reduction context left
    requireCompatible reduction leftType StringType
    rightType <- infer depth reduction context right
    requireCompatible reduction rightType StringType
    Right BoolType
  infer (S depth) reduction context (IOType ty) = do
    level <- sortOf depth reduction context ty
    Right (Universe level)
  infer (S depth) reduction context (IOPure value) = do
    ty <- infer depth reduction context value
    Right (IOType ty)
  infer (S depth) reduction context (WriteLine text) = do
    ty <- infer depth reduction context text
    requireCompatible reduction ty StringType
    Right (IOType UnitType)
  infer (S depth) reduction context (IOBind a b action next) = do
    _ <- sortOf depth reduction context a
    _ <- sortOf depth reduction context b
    actionType <- infer depth reduction context action
    requireCompatible reduction actionType (IOType a)
    nextType <- infer depth reduction context next
    requireCompatible reduction nextType (Pi Linear a (weaken (IOType b)))
    Right (IOType b)
  infer (S depth) reduction context (BoolCase condition yes no) = do
    conditionType <- infer depth reduction context condition
    requireCompatible reduction conditionType BoolType
    yesType <- infer depth reduction context yes
    noType <- infer depth reduction context no
    case betaCompare reduction yesType noType of
      EqualNormalForms => Right yesType
      DifferentNormalForms => Left (BranchTypeMismatch yesType noType)
      Inconclusive => Left ReductionLimit
  infer (S depth) reduction context (NominalType key indices shape) = do
    nominalIndices depth reduction context indices
    level <- sortOf depth reduction context shape
    exposed <- exposeType reduction shape
    case exposed of
      VariantType _ => Right (Universe level)
      _ => Left (NominalError "nominal shape must expose a variant type")
  infer (S depth) reduction context (NominalValue annotation value) = do
    _ <- sortOf depth reduction context annotation
    exposed <- exposeType reduction annotation
    case exposed of
      NominalType _ _ shape => do
        actual <- infer depth reduction context value
        requireCompatible reduction actual shape
        Right annotation
      _ => Left (NominalError "nominal value annotation must expose a nominal type")
  infer (S depth) reduction context (NominalCase motive scrutinee branch) = do
    ty <- infer depth reduction context scrutinee
    exposed <- exposeType reduction ty
    case exposed of
      NominalType _ _ shape => do
        motiveType <- infer depth reduction context motive
        exposedMotive <- exposeType reduction motiveType
        case exposedMotive of
          Pi Erased domain result => do
            requireCompatible reduction domain exposed
            resultSort <- exposeType reduction result
            case resultSort of
              Universe _ => Right ()
              _ => Left (NominalError "nominal motive must return a universe")
          _ => Left (NominalError "nominal motive must have an erased matching domain")
        actual <- infer depth reduction context branch
        requireCompatible reduction actual
          (Pi Linear shape (Apply (weaken motive) (NominalValue (weaken exposed) (Variable FZ))))
        Right (Apply motive scrutinee)
      _ => Left (NominalError "nominal case scrutinee must have a nominal type")
  infer (S depth) reduction context (VariantType []) = Left (VariantError "empty alternatives are not admitted")
  infer (S depth) reduction context (VariantType arms) = Universe <$> variantSort depth reduction context arms
  infer (S depth) reduction context (VariantValue annotation tag payload) = do
    _ <- sortOf depth reduction context annotation
    exposed <- exposeType reduction annotation
    case exposed of
      VariantType arms => case (variantAt tag arms, payload) of
        (Just Nothing, Nothing) => Right annotation
        (Just (Just (_, domain)), Just value) => do
          actual <- infer depth reduction context value
          requireCompatible reduction actual domain
          Right annotation
        _ => Left (VariantError "constructor tag or payload arity is invalid")
      _ => Left (VariantError "constructor annotation must expose a variant type")
  infer (S depth) reduction context (VariantCase motive scrutinee branches) = do
    ty <- infer depth reduction context scrutinee
    exposed <- exposeType reduction ty
    case exposed of
      VariantType arms => do
        motiveType <- infer depth reduction context motive
        exposedMotive <- exposeType reduction motiveType
        case exposedMotive of
          Pi Erased domain result => do
            requireCompatible reduction domain exposed
            resultSort <- exposeType reduction result
            case resultSort of
              Universe _ => Right ()
              _ => Left (VariantError "motive must return a universe")
          _ => Left (VariantError "motive must have an erased matching domain")
        variantBranches depth reduction context motive exposed 0 arms branches
        Right (Apply motive scrutinee)
      _ => Left (VariantError "case scrutinee must have a variant type")
  infer (S depth) reduction context (BoxType q domain) = do
    level <- sortOf depth reduction context domain
    Right (Universe level)
  infer (S depth) reduction context (BoxValue annotation value) = do
    _ <- sortOf depth reduction context annotation
    exposed <- exposeType reduction annotation
    case exposed of
      BoxType q domain => do
        valueType <- infer depth reduction context value
        requireCompatible reduction valueType domain
        Right annotation
      _ => Left (ExpectedBoxType exposed)
  infer (S depth) reduction context (BoxCase motive scrutinee branch) = do
    scrutineeType <- infer depth reduction context scrutinee
    exposed <- exposeType reduction scrutineeType
    case exposed of
      BoxType q domain => do
        motiveType <- infer depth reduction context motive
        motiveHead <- exposeType reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible reduction parameter scrutineeType
            resultHead <- exposeType reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (ExpectedBoxMotive motiveHead)
        let packed = BoxValue (weaken scrutineeType) (Variable FZ)
        let resultType = Apply (weaken motive) packed
        branchType <- infer depth reduction context branch
        requireCompatible reduction branchType (Pi q domain resultType)
        Right (Apply motive scrutinee)
      _ => Left (ExpectedBoxType exposed)
  infer (S depth) reduction context (Sigma q r domain body) = do
    domainLevel <- sortOf depth reduction context domain
    bodyLevel <- sortOf depth reduction (Extend context q domain) body
    Right (Universe (max domainLevel bodyLevel))
  infer (S depth) reduction context (PairCase motive scrutinee branch) = do
    scrutineeType <- infer depth reduction context scrutinee
    exposed <- exposeType reduction scrutineeType
    case exposed of
      Sigma q r domain body => do
        motiveType <- infer depth reduction context motive
        motiveHead <- exposeType reduction motiveType
        case motiveHead of
          Pi Erased parameter result => do
            requireCompatible reduction parameter scrutineeType
            resultHead <- exposeType reduction result
            case resultHead of
              Universe _ => Right ()
              _ => Left (ExpectedUniverse resultHead)
          _ => Left (ExpectedPairMotive motiveHead)
        let packed = PairValue (weaken (weaken scrutineeType))
                               (Variable (FS FZ)) (Variable FZ)
        let resultType = Apply (weaken (weaken motive)) packed
        branchType <- infer depth reduction context branch
        requireCompatible reduction branchType (Pi q domain (Pi r body resultType))
        Right (Apply motive scrutinee)
      _ => Left (ExpectedPairType exposed)
  infer (S depth) reduction context (PairValue annotation first second) = do
    _ <- sortOf depth reduction context annotation
    exposed <- exposeType reduction annotation
    case exposed of
      Sigma q r domain body => do
        firstType <- infer depth reduction context first
        requireCompatible reduction firstType domain
        secondType <- infer depth reduction context second
        requireCompatible reduction secondType (instantiateTerm first body)
        Right annotation
      _ => Left (ExpectedPairType exposed)
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
      _ => Left (ExpectedFunction exposed)

  infer (S depth) reduction context (UnitCase scrutinee body) = do
    scrutineeType <- infer depth reduction context scrutinee
    requireCompatible reduction scrutineeType UnitType
    infer depth reduction context body

  nominalIndices : Nat -> Nat -> Context n -> List (Term n) -> Either CheckError ()
  nominalIndices _ _ _ [] = Right ()
  nominalIndices Z _ _ (_ :: _) = Left CheckingLimit
  nominalIndices (S depth) reduction context (index :: rest) = do
    _ <- infer depth reduction context index
    nominalIndices depth reduction context rest

  variantSort : Nat -> Nat -> Context n -> List (Maybe (Quantity, Term n)) -> Either CheckError Nat
  variantSort depth reduction context [] = Right 0
  variantSort Z reduction context (_ :: _) = Left CheckingLimit
  variantSort (S depth) reduction context (Nothing :: rest) = variantSort depth reduction context rest
  variantSort (S depth) reduction context (Just (_, ty) :: rest) = do
    level <- sortOf depth reduction context ty
    remaining <- variantSort depth reduction context rest
    Right (max level remaining)

  variantBranches : Nat -> Nat -> Context n -> Term n -> Term n -> Nat ->
                    List (Maybe (Quantity, Term n)) -> List (Term n) -> Either CheckError ()
  variantBranches depth reduction context motive ty tag [] [] = Right ()
  variantBranches Z reduction context motive ty tag (_ :: _) (_ :: _) = Left CheckingLimit
  variantBranches (S depth) reduction context motive ty tag (arm :: arms) (branch :: branches) = do
    actual <- infer depth reduction context branch
    requireCompatible reduction actual (variantBranchType motive ty tag arm)
    variantBranches depth reduction context motive ty (S tag) arms branches
  variantBranches _ _ _ _ _ _ _ _ = Left (VariantError "case requires exactly one branch per alternative")

  sortOf : Nat -> Nat -> Context n -> Term n -> Either CheckError Nat
  sortOf depth reduction context term = do
    ty <- infer depth reduction context term
    exposed <- exposeType reduction ty
    case exposed of
      Universe level => Right level
      _ => Left (ExpectedUniverse exposed)

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
