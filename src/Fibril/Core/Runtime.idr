-- Experimental ordinary runtime usage checking, not a soundness claim.
-- Theory: ATKEY18 sec. 2; local policy/departures: docs/runtime-checker.md.
module Fibril.Core.Runtime

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Usage
import Fibril.Core.WeakHead
import Fibril.Core.Erased

%default total

||| Failures preserve typing/exhaustion errors and identify resource mismatches.
public export
data RuntimeError
  = TypingError CheckError
  | BoundUsage Quantity Quantity
  | ContextUsage Nat Quantity Quantity
  | RuntimeTypeExpression

public export
Show RuntimeError where
  show (TypingError err) = show err
  show (BoundUsage expected observed) =
    "Binder usage: expected " ++ show expected ++ ", observed " ++ show observed
  show (ContextUsage i expected observed) =
    "Variable " ++ show i ++ ": expected " ++ show expected ++ ", observed " ++ show observed
  show RuntimeTypeExpression = "Runtime type expressions (universe/Pi/Sigma/Box/Variant/Nominal/Unit/Bool/String/IO/FileHandle) are not supported"

liftTyping : Either CheckError a -> Either RuntimeError a
liftTyping (Left err) = Left (TypingError err)
liftTyping (Right value) = Right value

-- Types/annotations have already been checked through erased inference.
-- Do not validate full ambient usage for each subterm: siblings share resources.
mutual
  analyze : {n : Nat} -> Nat -> Nat -> Context n -> Term n ->
            Either RuntimeError (Usage n)
  analyze Z reduction context term = Left (TypingError CheckingLimit)
  analyze (S depth) reduction context (Variable i) = Right (variableUsage RuntimeMode i)
  analyze (S depth) reduction context (Universe _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context UnitType = Left RuntimeTypeExpression
  analyze (S depth) reduction context UnitValue = Right zeroUsage
  analyze (S depth) reduction context BoolType = Left RuntimeTypeExpression
  analyze (S depth) reduction context BoolTrue = Right zeroUsage
  analyze (S depth) reduction context BoolFalse = Right zeroUsage
  analyze (S depth) reduction context NatType = Left RuntimeTypeExpression
  analyze (S depth) reduction context NatZero = Right zeroUsage
  analyze (S depth) reduction context (NatSucc value) = analyze depth reduction context value
  analyze (S depth) reduction context (NatRec motive base next value) = do
    baseUsage <- analyze depth reduction context base
    nextUsage <- analyze depth reduction context next
    valueUsage <- analyze depth reduction context value
    Right (combineUsage valueUsage (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze (S depth) reduction context (NatRecRuntime motive base next value) = do
    baseUsage <- analyze depth reduction context base
    nextUsage <- analyze depth reduction context next
    valueUsage <- analyze depth reduction context value
    Right (combineUsage (scaleUsage Unrestricted valueUsage)
           (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze (S depth) reduction context (RecType _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (RecEnd _) = Right zeroUsage
  analyze (S depth) reduction context (RecMore _ tail) = analyze depth reduction context tail
  analyze (S depth) reduction context (RecFold motive base next value) = do
    baseUsage <- analyze depth reduction context base
    nextUsage <- analyze depth reduction context next
    valueUsage <- analyze depth reduction context value
    Right (combineUsage valueUsage (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze (S depth) reduction context (RecCase motive value base more) = do
    valueUsage <- analyze depth reduction context value
    baseUsage <- analyze depth reduction context base
    moreUsage <- analyze depth reduction context more
    Right (combineUsage valueUsage (joinUsage baseUsage moreUsage))
  analyze (S depth) reduction context (SeqType _ _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (SeqNil _) = Right zeroUsage
  analyze (S depth) reduction context (SeqCons _ head tail) = do
    headUsage <- analyze depth reduction context head
    tailUsage <- analyze depth reduction context tail
    Right (combineUsage headUsage tailUsage)
  analyze (S depth) reduction context (SeqFold motive base next value) = do
    baseUsage <- analyze depth reduction context base
    nextUsage <- analyze depth reduction context next
    valueUsage <- analyze depth reduction context value
    Right (combineUsage valueUsage (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze (S depth) reduction context (SeqCase motive value base cons) = do
    valueUsage <- analyze depth reduction context value
    baseUsage <- analyze depth reduction context base
    consUsage <- analyze depth reduction context cons
    Right (combineUsage valueUsage (joinUsage baseUsage consUsage))
  analyze (S depth) reduction context ReadLine = Right zeroUsage
  analyze (S depth) reduction context (FileHandleValue _ _) = Right zeroUsage
  analyze (S depth) reduction context (ReadInputFile handle) = analyze depth reduction context handle
  analyze (S depth) reduction context (BytesIndex a b) = do
    x <- analyze depth reduction context a
    y <- analyze depth reduction context b
    Right (combineUsage x y)
  analyze (S depth) reduction context (BytesSlice a b c) = do
    x <- analyze depth reduction context a
    y <- analyze depth reduction context b
    z <- analyze depth reduction context c
    Right (combineUsage x (combineUsage y z))
  analyze (S depth) reduction context (UTF8Encode x) = analyze depth reduction context x
  analyze (S depth) reduction context (UTF8Decode x) = analyze depth reduction context x
  analyze (S depth) reduction context BytesType = Left RuntimeTypeExpression
  analyze (S depth) reduction context (BytesValue _) = Right zeroUsage
  analyze (S depth) reduction context (BytesLength x) = analyze depth reduction context x
  analyze (S depth) reduction context (BytesOctet x) = analyze depth reduction context x
  analyze (S depth) reduction context (BytesAppend a b) = do
    leftUsage <- analyze depth reduction context a
    rightUsage <- analyze depth reduction context b
    Right (combineUsage leftUsage rightUsage)
  analyze (S depth) reduction context StringType = Left RuntimeTypeExpression
  analyze (S depth) reduction context (StringValue _) = Right zeroUsage
  analyze (S depth) reduction context (StringAppend left right) = do
    leftUsage <- analyze depth reduction context left
    rightUsage <- analyze depth reduction context right
    Right (combineUsage leftUsage rightUsage)
  analyze (S depth) reduction context (StringEqual left right) = do
    leftUsage <- analyze depth reduction context left
    rightUsage <- analyze depth reduction context right
    Right (combineUsage leftUsage rightUsage)
  analyze (S depth) reduction context (WithInputFile result path body) = do
    pathUsage <- analyze depth reduction context path
    bodyUsage <- analyze depth reduction context body
    -- Open failure skips the callback: it cannot own captured linear resources.
    Right (combineUsage pathUsage (scaleUsage Unrestricted bodyUsage))
  analyze (S depth) reduction context (IOType _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (FileHandleType _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (IOPure value) = analyze depth reduction context value
  analyze (S depth) reduction context (WriteLine text) = analyze depth reduction context text
  analyze (S depth) reduction context (IOBind a b action next) = do
    actionUsage <- analyze depth reduction context action
    nextUsage <- analyze depth reduction context next
    Right (combineUsage actionUsage nextUsage)
  analyze (S depth) reduction context (BoolCase condition yes no) = do
    conditionUsage <- analyze depth reduction context condition
    yesUsage <- analyze depth reduction context yes
    noUsage <- analyze depth reduction context no
    Right (combineUsage conditionUsage (joinUsage yesUsage noUsage))
  analyze (S depth) reduction context (NominalType _ _ _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (NominalValue annotation value) = analyze depth reduction context value
  analyze (S depth) reduction context (NominalCase motive value branch) = do
    valueUsage <- analyze depth reduction context value
    branchUsage <- analyze depth reduction context branch
    Right (combineUsage valueUsage branchUsage)
  analyze (S depth) reduction context (VariantType _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (VariantValue annotation tag payload) = do
    exposed <- case weakHead reduction annotation of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      VariantType arms => case (variantAt tag arms, payload) of
        (Just Nothing, Nothing) => Right zeroUsage
        (Just (Just (Erased, _)), Just _) => Right zeroUsage
        (Just (Just (q, _)), Just value) => scaleUsage q <$> analyze depth reduction context value
        _ => Left (TypingError (VariantError "invalid runtime tag or payload arity"))
      _ => Left (TypingError (VariantError "runtime constructor requires variant type"))
  analyze (S depth) reduction context (VariantCase motive value branches) = do
    valueUsage <- analyze depth reduction context value
    branchUsage <- variantUsages depth reduction context branches
    Right (combineUsage valueUsage branchUsage)
  analyze (S depth) reduction context (BoxType _ _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (BoxCase motive scrutinee branch) = do
    valueUsage <- analyze depth reduction context scrutinee
    branchUsage <- analyze depth reduction context branch
    Right (combineUsage valueUsage branchUsage)
  analyze (S depth) reduction context (BoxValue annotation value) = do
    exposed <- case weakHead reduction annotation of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      BoxType q _ => do
        valueUsage <- case q of
          Erased => Right zeroUsage
          _ => analyze depth reduction context value
        Right (scaleUsage q valueUsage)
      _ => Left (TypingError (ExpectedBoxType exposed))
  analyze (S depth) reduction context (Sigma _ _ _ _) = Left RuntimeTypeExpression
  -- The branch has already been checked against the Sigma's exact Pi quantities.
  -- Its ordinary lambda analysis discharges both fields; it is invoked once.
  analyze (S depth) reduction context (PairCase motive scrutinee branch) = do
    scrutineeUsage <- analyze depth reduction context scrutinee
    branchUsage <- analyze depth reduction context branch
    Right (combineUsage scrutineeUsage branchUsage)
  analyze (S depth) reduction context (PairValue annotation first second) = do
    exposed <- case weakHead reduction annotation of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      Sigma q r _ _ => do
        firstUsage <- case q of
          Erased => Right zeroUsage
          _ => analyze depth reduction context first
        secondUsage <- case r of
          Erased => Right zeroUsage
          _ => analyze depth reduction context second
        Right (combineUsage (scaleUsage q firstUsage) (scaleUsage r secondUsage))
      _ => Left (TypingError (ExpectedPairType exposed))
  analyze (S depth) reduction context (Pi _ _ _) = Left RuntimeTypeExpression
  analyze (S depth) reduction context (Lambda q domain body) = do
    bodyUsage <- analyze depth reduction (Extend context q domain) body
    case discharge RuntimeMode q bodyUsage of
      Right outer => Right outer
      Left err => Left (BoundUsage err.expected err.observed)
  analyze (S depth) reduction context (Apply function argument) = do
    functionType <- liftTyping (inferErased depth reduction context function)
    exposed <- case weakHead reduction functionType of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      Pi q domain body => do
        functionUsage <- analyze depth reduction context function
        argumentUsage <- case q of
          Erased => Right zeroUsage
          _ => analyze depth reduction context argument
        Right (combineUsage functionUsage (scaleUsage q argumentUsage))
      _ => Left (TypingError (ExpectedFunction exposed))

  analyze (S depth) reduction context (UnitCase scrutinee body) = do
    scrutineeUsage <- analyze depth reduction context scrutinee
    bodyUsage <- analyze depth reduction context body
    Right (combineUsage scrutineeUsage bodyUsage)


  variantUsages : {n : Nat} -> Nat -> Nat -> Context n -> List (Term n) -> Either RuntimeError (Usage n)
  variantUsages _ _ _ [] = Left (TypingError (VariantError "empty runtime branches"))
  variantUsages Z _ _ (_ :: _) = Left (TypingError CheckingLimit)
  variantUsages (S depth) reduction context [branch] = analyze depth reduction context branch
  variantUsages (S depth) reduction context (branch :: following@(_ :: _)) = do
    usage <- analyze depth reduction context branch
    rest <- variantUsages depth reduction context following
    Right (joinUsage usage rest)

||| A successful prototype result includes its ordinary type and observed usage.
||| It is not a proof of erasure correctness or quantitative preservation.
public export
record RuntimeResult (n : Nat) where
  constructor RuntimeChecked
  inferredType : Term n
  usage : Usage n

||| Type-check erased first, then check runtime usage and ambient permissions.
||| Erased arguments are fully type checked but not traversed as runtime values.
public export
inferRuntime : {n : Nat} -> Nat -> Nat -> Context n -> Term n ->
               Either RuntimeError (RuntimeResult n)
inferRuntime depth reduction context term = do
  ty <- liftTyping (inferErased depth reduction context term)
  observed <- analyze depth reduction context term
  case validateUsage RuntimeMode context observed of
    Right () => Right (RuntimeChecked ty observed)
    Left err => Left (ContextUsage (finToNat err.variable)
                                  err.mismatch.expected err.mismatch.observed)

||| Validate the expected type and beta comparison before runtime usage checking.
public export
checkRuntime : {n : Nat} -> Nat -> Nat -> Context n -> Term n -> Term n ->
               Either RuntimeError (RuntimeResult n)
checkRuntime depth reduction context term expected = do
  liftTyping (checkErased depth reduction context term expected)
  inferRuntime depth reduction context term
