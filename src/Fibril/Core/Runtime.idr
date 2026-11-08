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

||| Runtime admission extends erased admission with checked closed usage.
||| The constructor is private; an erased-only context cannot authorize execution.
export
data RuntimeGlobals : Type where
  CheckedRuntimeGlobals : GlobalContext -> RuntimeGlobals

public export
emptyRuntimeGlobals : RuntimeGlobals
emptyRuntimeGlobals = CheckedRuntimeGlobals emptyGlobals

public export
erasedGlobals : RuntimeGlobals -> GlobalContext
erasedGlobals (CheckedRuntimeGlobals globals) = globals

-- Types/annotations have already been checked through erased inference.
-- Do not validate full ambient usage for each subterm: siblings share resources.
mutual
  analyze : RuntimeGlobals -> {n : Nat} -> Nat -> Nat -> Context n -> Term n ->
            Either RuntimeError (Usage n)
  analyze globals Z reduction context term = Left (TypingError CheckingLimit)
  analyze globals (S depth) reduction context (GlobalRef key) =
    case globalEntry (erasedGlobals globals) key of
      Just (Unrestricted, _, _) => Right zeroUsage
      Just (Erased, _, _) => Left (TypingError (GlobalError "erased global used at runtime"))
      _ => Left (TypingError (GlobalError ("unavailable runtime global " ++ show key)))
  analyze globals (S depth) reduction context (Variable i) = Right (variableUsage RuntimeMode i)
  analyze globals (S depth) reduction context (Universe _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context UnitType = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context UnitValue = Right zeroUsage
  analyze globals (S depth) reduction context BoolType = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context BoolTrue = Right zeroUsage
  analyze globals (S depth) reduction context BoolFalse = Right zeroUsage
  analyze globals (S depth) reduction context NatType = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context NatZero = Right zeroUsage
  analyze globals (S depth) reduction context (NatSucc value) = analyze globals depth reduction context value
  analyze globals (S depth) reduction context (NatRec motive base next value) = do
    baseUsage <- analyze globals depth reduction context base
    nextUsage <- analyze globals depth reduction context next
    valueUsage <- analyze globals depth reduction context value
    Right (combineUsage valueUsage (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze globals (S depth) reduction context (NatRecRuntime motive base next value) = do
    baseUsage <- analyze globals depth reduction context base
    nextUsage <- analyze globals depth reduction context next
    valueUsage <- analyze globals depth reduction context value
    Right (combineUsage (scaleUsage Unrestricted valueUsage)
           (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze globals (S depth) reduction context (RecType _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (RecEnd _) = Right zeroUsage
  analyze globals (S depth) reduction context (RecMore _ tail) = analyze globals depth reduction context tail
  analyze globals (S depth) reduction context (RecFold motive base next value) = do
    baseUsage <- analyze globals depth reduction context base
    nextUsage <- analyze globals depth reduction context next
    valueUsage <- analyze globals depth reduction context value
    Right (combineUsage valueUsage (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze globals (S depth) reduction context (RecCase motive value base more) = do
    valueUsage <- analyze globals depth reduction context value
    baseUsage <- analyze globals depth reduction context base
    moreUsage <- analyze globals depth reduction context more
    Right (combineUsage valueUsage (joinUsage baseUsage moreUsage))
  analyze globals (S depth) reduction context (NatCase motive value base more) = do
    moreType <- liftTyping (inferErasedGlobals (erasedGlobals globals) depth reduction context more)
    exposed <- case weakHeadGlobals (globalValue (erasedGlobals globals)) reduction moreType of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      Pi q _ _ => do
        valueUsage <- analyze globals depth reduction context value
        baseUsage <- analyze globals depth reduction context base
        moreUsage <- analyze globals depth reduction context more
        Right (combineUsage (scaleUsage q valueUsage) (joinUsage baseUsage moreUsage))
      _ => Left (TypingError (ExpectedFunction exposed))
  analyze globals (S depth) reduction context (SeqType _ _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (SeqNil _) = Right zeroUsage
  analyze globals (S depth) reduction context (SeqCons _ head tail) = do
    headUsage <- analyze globals depth reduction context head
    tailUsage <- analyze globals depth reduction context tail
    Right (combineUsage headUsage tailUsage)
  analyze globals (S depth) reduction context (SeqFold motive base next value) = do
    baseUsage <- analyze globals depth reduction context base
    nextUsage <- analyze globals depth reduction context next
    valueUsage <- analyze globals depth reduction context value
    Right (combineUsage valueUsage (combineUsage baseUsage (scaleUsage Unrestricted nextUsage)))
  analyze globals (S depth) reduction context (SeqCase motive value base cons) = do
    valueUsage <- analyze globals depth reduction context value
    baseUsage <- analyze globals depth reduction context base
    consUsage <- analyze globals depth reduction context cons
    Right (combineUsage valueUsage (joinUsage baseUsage consUsage))
  analyze globals (S depth) reduction context (IterateBinary stateType resultType count step initial) = do
    countUsage <- analyze globals depth reduction context count
    stepUsage <- analyze globals depth reduction context step
    initialUsage <- analyze globals depth reduction context initial
    Right (combineUsage countUsage (combineUsage (scaleUsage Unrestricted stepUsage) initialUsage))
  analyze globals (S depth) reduction context (ReadBytes x) = analyze globals depth reduction context x
  analyze globals (S depth) reduction context (WriteBytes x) = analyze globals depth reduction context x
  analyze globals (S depth) reduction context RejectBytes = Right zeroUsage
  analyze globals (S depth) reduction context FlushBytes = Right zeroUsage
  analyze globals (S depth) reduction context ReadLine = Right zeroUsage
  analyze globals (S depth) reduction context (FileHandleValue _ _) = Right zeroUsage
  analyze globals (S depth) reduction context (ReadInputFile handle) = analyze globals depth reduction context handle
  analyze globals (S depth) reduction context (BytesLengthIs a b) = do
    x <- analyze globals depth reduction context a
    y <- analyze globals depth reduction context b
    Right (combineUsage x y)
  analyze globals (S depth) reduction context (BytesIndex a b) = do
    x <- analyze globals depth reduction context a
    y <- analyze globals depth reduction context b
    Right (combineUsage x y)
  analyze globals (S depth) reduction context (BytesSlice a b c) = do
    x <- analyze globals depth reduction context a
    y <- analyze globals depth reduction context b
    z <- analyze globals depth reduction context c
    Right (combineUsage x (combineUsage y z))
  analyze globals (S depth) reduction context (UTF8Encode x) = analyze globals depth reduction context x
  analyze globals (S depth) reduction context (UTF8Decode x) = analyze globals depth reduction context x
  analyze globals (S depth) reduction context BytesType = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (BytesValue _) = Right zeroUsage
  analyze globals (S depth) reduction context (BytesShare x) = analyze globals depth reduction context x
  analyze globals (S depth) reduction context (BytesLength x) = analyze globals depth reduction context x
  analyze globals (S depth) reduction context (BytesOctet x) = analyze globals depth reduction context x
  -- The body is applied exactly once, so its permissions are not scaled.
  analyze globals (S depth) reduction context (WithRegion resultType body) = do
    liftTyping (checkRegionResultGlobals (erasedGlobals globals) reduction resultType)
    analyze globals depth reduction context body
  analyze globals (S depth) reduction context (BytesAppend a b) = do
    leftUsage <- analyze globals depth reduction context a
    rightUsage <- analyze globals depth reduction context b
    Right (combineUsage leftUsage rightUsage)
  analyze globals (S depth) reduction context StringType = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (StringValue _) = Right zeroUsage
  analyze globals (S depth) reduction context (StringAppend left right) = do
    leftUsage <- analyze globals depth reduction context left
    rightUsage <- analyze globals depth reduction context right
    Right (combineUsage leftUsage rightUsage)
  analyze globals (S depth) reduction context (StringEqual left right) = do
    leftUsage <- analyze globals depth reduction context left
    rightUsage <- analyze globals depth reduction context right
    Right (combineUsage leftUsage rightUsage)
  analyze globals (S depth) reduction context (WithInputFile result path body) = do
    pathUsage <- analyze globals depth reduction context path
    bodyUsage <- analyze globals depth reduction context body
    -- Open failure skips the callback: it cannot own captured linear resources.
    Right (combineUsage pathUsage (scaleUsage Unrestricted bodyUsage))
  analyze globals (S depth) reduction context (IOType _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (FileHandleType _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (IOPure value) = analyze globals depth reduction context value
  analyze globals (S depth) reduction context (WriteLine text) = analyze globals depth reduction context text
  analyze globals (S depth) reduction context (IOBind a b action next) = do
    actionUsage <- analyze globals depth reduction context action
    nextUsage <- analyze globals depth reduction context next
    Right (combineUsage actionUsage nextUsage)
  analyze globals (S depth) reduction context (BoolCase condition yes no) = do
    conditionUsage <- analyze globals depth reduction context condition
    yesUsage <- analyze globals depth reduction context yes
    noUsage <- analyze globals depth reduction context no
    Right (combineUsage conditionUsage (joinUsage yesUsage noUsage))
  analyze globals (S depth) reduction context (NominalType _ _ _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (NominalValue annotation value) = analyze globals depth reduction context value
  analyze globals (S depth) reduction context (NominalCase motive value branch) = do
    valueUsage <- analyze globals depth reduction context value
    branchUsage <- analyze globals depth reduction context branch
    Right (combineUsage valueUsage branchUsage)
  analyze globals (S depth) reduction context (VariantType _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (VariantValue annotation tag payload) = do
    exposed <- case weakHeadGlobals (globalValue (erasedGlobals globals)) reduction annotation of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      VariantType arms => case (variantAt tag arms, payload) of
        (Just Nothing, Nothing) => Right zeroUsage
        (Just (Just (Erased, _)), Just _) => Right zeroUsage
        (Just (Just (q, _)), Just value) => scaleUsage q <$> analyze globals depth reduction context value
        _ => Left (TypingError (VariantError "invalid runtime tag or payload arity"))
      _ => Left (TypingError (VariantError "runtime constructor requires variant type"))
  -- Typing is not implemented (docs/general-recursive-data-plan.md, phase 3): refuse.
  analyze globals (S depth) reduction context (DataType _) = Left (TypingError (RecursiveDataError "general recursive data typing is not implemented"))
  analyze globals (S depth) reduction context (DataCon _ _ _) = Left (TypingError (RecursiveDataError "general recursive data typing is not implemented"))
  analyze globals (S depth) reduction context (DataCase _ _ _ _) = Left (TypingError (RecursiveDataError "general recursive data typing is not implemented"))
  analyze globals (S depth) reduction context (VariantCase motive value branches) = do
    valueUsage <- analyze globals depth reduction context value
    branchUsage <- variantUsages globals depth reduction context branches
    Right (combineUsage valueUsage branchUsage)
  analyze globals (S depth) reduction context (BoxType _ _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (BoxCase motive scrutinee branch) = do
    valueUsage <- analyze globals depth reduction context scrutinee
    branchUsage <- analyze globals depth reduction context branch
    Right (combineUsage valueUsage branchUsage)
  analyze globals (S depth) reduction context (BoxValue annotation value) = do
    exposed <- case weakHeadGlobals (globalValue (erasedGlobals globals)) reduction annotation of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      BoxType q _ => do
        valueUsage <- case q of
          Erased => Right zeroUsage
          _ => analyze globals depth reduction context value
        Right (scaleUsage q valueUsage)
      _ => Left (TypingError (ExpectedBoxType exposed))
  analyze globals (S depth) reduction context (Sigma _ _ _ _) = Left RuntimeTypeExpression
  -- The branch has already been checked against the Sigma's exact Pi quantities.
  -- Its ordinary lambda analysis discharges both fields; it is invoked once.
  analyze globals (S depth) reduction context (PairCase motive scrutinee branch) = do
    scrutineeUsage <- analyze globals depth reduction context scrutinee
    branchUsage <- analyze globals depth reduction context branch
    Right (combineUsage scrutineeUsage branchUsage)
  analyze globals (S depth) reduction context (PairValue annotation first second) = do
    exposed <- case weakHeadGlobals (globalValue (erasedGlobals globals)) reduction annotation of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      Sigma q r _ _ => do
        firstUsage <- case q of
          Erased => Right zeroUsage
          _ => analyze globals depth reduction context first
        secondUsage <- case r of
          Erased => Right zeroUsage
          _ => analyze globals depth reduction context second
        Right (combineUsage (scaleUsage q firstUsage) (scaleUsage r secondUsage))
      _ => Left (TypingError (ExpectedPairType exposed))
  analyze globals (S depth) reduction context (Pi _ _ _) = Left RuntimeTypeExpression
  analyze globals (S depth) reduction context (Lambda q domain body) = do
    bodyUsage <- analyze globals depth reduction (Extend context q domain) body
    case discharge RuntimeMode q bodyUsage of
      Right outer => Right outer
      Left err => Left (BoundUsage err.expected err.observed)
  -- Fix duplicates its closure on every unfolding, so captured outer variables
  -- are scaled by Unrestricted; linear captures then fail context validation.
  analyze globals (S depth) reduction context (Fix ty body) = do
    bodyUsage <- analyze globals depth reduction (Extend context Unrestricted ty) body
    case discharge RuntimeMode Unrestricted bodyUsage of
      Right outer => Right (scaleUsage Unrestricted outer)
      Left err => Left (BoundUsage err.expected err.observed)
  analyze globals (S depth) reduction context (Apply function argument) = do
    functionType <- liftTyping (inferErasedGlobals (erasedGlobals globals) depth reduction context function)
    exposed <- case weakHeadGlobals (globalValue (erasedGlobals globals)) reduction functionType of
      HeadForm ty => Right ty
      HeadLimit _ => Left (TypingError ReductionLimit)
    case exposed of
      Pi q domain body => do
        functionUsage <- analyze globals depth reduction context function
        argumentUsage <- case q of
          Erased => Right zeroUsage
          _ => analyze globals depth reduction context argument
        Right (combineUsage functionUsage (scaleUsage q argumentUsage))
      _ => Left (TypingError (ExpectedFunction exposed))

  analyze globals (S depth) reduction context (UnitCase scrutinee body) = do
    scrutineeUsage <- analyze globals depth reduction context scrutinee
    bodyUsage <- analyze globals depth reduction context body
    Right (combineUsage scrutineeUsage bodyUsage)


  variantUsages : RuntimeGlobals -> {n : Nat} -> Nat -> Nat -> Context n -> List (Term n) -> Either RuntimeError (Usage n)
  variantUsages globals _ _ _ [] = Left (TypingError (VariantError "empty runtime branches"))
  variantUsages globals Z _ _ (_ :: _) = Left (TypingError CheckingLimit)
  variantUsages globals (S depth) reduction context [branch] = analyze globals depth reduction context branch
  variantUsages globals (S depth) reduction context (branch :: following@(_ :: _)) = do
    usage <- analyze globals depth reduction context branch
    rest <- variantUsages globals depth reduction context following
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
inferRuntimeGlobals : RuntimeGlobals -> {n : Nat} -> Nat -> Nat -> Context n -> Term n ->
               Either RuntimeError (RuntimeResult n)
inferRuntimeGlobals globals depth reduction context term = do
  ty <- liftTyping (inferErasedGlobals (erasedGlobals globals) depth reduction context term)
  observed <- analyze globals depth reduction context term
  case validateUsage RuntimeMode context observed of
    Right () => Right (RuntimeChecked ty observed)
    Left err => Left (ContextUsage (finToNat err.variable)
                                  err.mismatch.expected err.mismatch.observed)

||| Validate the expected type and beta comparison before runtime usage checking.
public export
checkRuntimeGlobals : RuntimeGlobals -> {n : Nat} -> Nat -> Nat -> Context n -> Term n -> Term n ->
               Either RuntimeError (RuntimeResult n)
checkRuntimeGlobals globals depth reduction context term expected = do
  liftTyping (checkErasedGlobals (erasedGlobals globals) depth reduction context term expected)
  inferRuntimeGlobals globals depth reduction context term

||| Check a declaration once, retaining its closed body and signature without
||| copying either into reference sites. Earlier declarations are immutable.
public export
extendRuntimeGlobals : Nat -> Nat -> RuntimeGlobals -> Nat -> Quantity -> Term 0 -> Term 0 ->
                      Either RuntimeError RuntimeGlobals
extendRuntimeGlobals depth reduction globals key q ty body = do
  next <- liftTyping (extendErasedGlobals depth reduction (erasedGlobals globals) key q ty body)
  case q of
    Erased => Right ()
    _ => do
      _ <- checkRuntimeGlobals globals depth reduction Empty body ty
      Right ()
  Right (CheckedRuntimeGlobals next)

public export
inferRuntime : {n : Nat} -> Nat -> Nat -> Context n -> Term n -> Either RuntimeError (RuntimeResult n)
inferRuntime = inferRuntimeGlobals emptyRuntimeGlobals

public export
checkRuntime : {n : Nat} -> Nat -> Nat -> Context n -> Term n -> Term n -> Either RuntimeError (RuntimeResult n)
checkRuntime = checkRuntimeGlobals emptyRuntimeGlobals
