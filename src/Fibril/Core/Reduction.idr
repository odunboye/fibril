-- Reference beta/data-case reduction for ordinary scoped syntax, not a typed evaluator.
-- Binding background: DEBRUIJN72; see docs/references.md and docs/reduction.md.
module Fibril.Core.Reduction

import Data.Fin
import public Fibril.Core.Reduction.Work
import Fibril.Core.Term
import Fibril.Data.Bytes
import Fibril.Source.UTF8
import Fibril.Core.Quantity

%default total

public export
encodeUTF8Value : String -> Term n
encodeUTF8Value text = case encodeUTF8 text of
  Left _ => VariantValue (utf8ResultType BytesType) 0 Nothing
  Right bytes => VariantValue (utf8ResultType BytesType) 1 (Just (BytesValue (fromList bytes)))

public export
decodeUTF8Value : Bytes -> Term n
decodeUTF8Value bytes = case decodeUTF8 (toList bytes) of
  Left _ => VariantValue (utf8ResultType StringType) 0 Nothing
  Right text => VariantValue (utf8ResultType StringType) 1 (Just (StringValue text))

||| Shared root selection, total even on malformed raw tags.
public export
variantContract : Nat -> Maybe (Term n) -> List (Term n) -> Maybe (Term n)
variantContract _ _ [] = Nothing
variantContract Z Nothing (branch :: _) = Just branch
variantContract Z (Just value) (branch :: _) = Just (Apply branch value)
variantContract (S tag) payload (_ :: rest) = variantContract tag payload rest

||| A constructor application of a general data family: key, index, leading parameter count and
||| every argument in order. Anything else is not a constructor spine.
public export
dataSpine : Term n -> Maybe (String, Nat, Nat, List (Term n))
dataSpine term = go term []
  where
    go : Term m -> List (Term m) -> Maybe (String, Nat, Nat, List (Term m))
    go (DataCon key index leading) args = Just (key, index, leading, args)
    go (Apply function argument) args = go function (argument :: args)
    go _ _ = Nothing

dropLeading : Nat -> List a -> List a
dropLeading Z xs = xs
dropLeading (S k) [] = []
dropLeading (S k) (_ :: xs) = dropLeading k xs

applyAll : Term n -> List (Term n) -> Term n
applyAll function [] = function
applyAll function (argument :: rest) = applyAll (Apply function argument) rest

branchAt : Nat -> List (Term n) -> Maybe (Term n)
branchAt _ [] = Nothing
branchAt Z (branch :: _) = Just branch
branchAt (S k) (_ :: rest) = branchAt k rest

||| Contract a case on a constructor of the same family: the chosen branch applied to the fields.
public export
dataContract : String -> Term n -> List (Term n) -> Maybe (Term n)
dataContract key value branches = case dataSpine value of
  Just (other, index, leading, args) =>
    if other == key
      then map (\branch => applyAll branch (dropLeading leading args)) (branchAt index branches)
      else Nothing
  Nothing => Nothing

-- Lift the existing Maybe step result through the chosen work policy.
mapStep : Functor m => (a -> b) -> m (Maybe a) -> m (Maybe b)
mapStep f = map (map f)

mutual
  ||| One leftmost full beta/data-case step, including domain annotations and binder bodies.
  ||| Nothing means reference normal form for this grammar, not well typed or valid.
  public export
  stepWithGlobals : NaturalWork m => (Nat -> Maybe (Term 0)) -> Term n -> m (Maybe (Term n))
  stepWithGlobals globals (GlobalRef key) = pure (map (rename absurd) (globals key))
  stepWithGlobals globals (Variable i) = pure Nothing
  stepWithGlobals globals (Universe l) = pure Nothing
  stepWithGlobals globals UnitType = pure Nothing
  stepWithGlobals globals UnitValue = pure Nothing
  stepWithGlobals globals BoolType = pure Nothing
  stepWithGlobals globals BoolTrue = pure Nothing
  stepWithGlobals globals BoolFalse = pure Nothing
  stepWithGlobals globals NatType = pure Nothing
  stepWithGlobals globals NatZero = pure Nothing
  stepWithGlobals globals (NatSucc value) = do
    visitSuccessor
    mapStep NatSucc (stepWithGlobals globals value)
  stepWithGlobals globals (NatRec motive base next NatZero) = pure (Just base)
  stepWithGlobals globals (NatRec motive base next (NatSucc value)) = do
    visitSuccessor
    pure (Just (Apply (Apply next value) (NatRec motive base next value)))
  stepWithGlobals globals (NatRec motive base next value) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (NatRec p base next value))
      Nothing => do
        reduced <- stepWithGlobals globals base
        case reduced of
          Just z => pure (Just (NatRec motive z next value))
          Nothing => do
            reduced <- stepWithGlobals globals next
            case reduced of
              Just s => pure (Just (NatRec motive base s value))
              Nothing => mapStep (NatRec motive base next) (stepWithGlobals globals value)
  stepWithGlobals globals (NatRecRuntime motive base next NatZero) = pure (Just base)
  stepWithGlobals globals (NatRecRuntime motive base next (NatSucc value)) = do
    visitSuccessor
    pure (Just (Apply (Apply next value) (NatRecRuntime motive base next value)))
  stepWithGlobals globals (NatRecRuntime motive base next value) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (NatRecRuntime p base next value))
      Nothing => do
        reduced <- stepWithGlobals globals base
        case reduced of
          Just z => pure (Just (NatRecRuntime motive z next value))
          Nothing => do
            reduced <- stepWithGlobals globals next
            case reduced of
              Just s => pure (Just (NatRecRuntime motive base s value))
              Nothing => mapStep (NatRecRuntime motive base next) (stepWithGlobals globals value)
  stepWithGlobals globals (RecType _) = pure Nothing
  stepWithGlobals globals (RecEnd ty) = mapStep RecEnd (stepWithGlobals globals ty)
  stepWithGlobals globals (RecMore ty tail) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (RecMore next tail))
      Nothing => mapStep (RecMore ty) (stepWithGlobals globals tail)
  stepWithGlobals globals (RecFold motive base next (RecEnd _)) = pure (Just base)
  stepWithGlobals globals (RecFold motive base next (RecMore _ tail)) =
    pure (Just (Apply (Apply next tail) (RecFold motive base next tail)))
  stepWithGlobals globals (RecFold motive base next value) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (RecFold p base next value))
      Nothing => do
        reduced <- stepWithGlobals globals base
        case reduced of
          Just z => pure (Just (RecFold motive z next value))
          Nothing => do
            reduced <- stepWithGlobals globals next
            case reduced of
              Just s => pure (Just (RecFold motive base s value))
              Nothing => mapStep (RecFold motive base next) (stepWithGlobals globals value)
  stepWithGlobals globals (RecCase motive (RecEnd _) base more) = pure (Just base)
  stepWithGlobals globals (RecCase motive (RecMore _ tail) base more) = pure (Just (Apply more tail))
  stepWithGlobals globals (RecCase motive value base more) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (RecCase p value base more))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just x => pure (Just (RecCase motive x base more))
          Nothing => do
            reduced <- stepWithGlobals globals base
            case reduced of
              Just z => pure (Just (RecCase motive value z more))
              Nothing => mapStep (RecCase motive value base) (stepWithGlobals globals more)
  stepWithGlobals globals (NatCase motive NatZero base more) = pure (Just base)
  stepWithGlobals globals (NatCase motive (NatSucc tail) base more) = do
    visitSuccessor
    pure (Just (Apply more tail))
  stepWithGlobals globals (NatCase motive value base more) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (NatCase p value base more))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just x => pure (Just (NatCase motive x base more))
          Nothing => do
            reduced <- stepWithGlobals globals base
            case reduced of
              Just z => pure (Just (NatCase motive value z more))
              Nothing => mapStep (NatCase motive value base) (stepWithGlobals globals more)
  stepWithGlobals globals (SeqType key element) = mapStep (SeqType key) (stepWithGlobals globals element)
  stepWithGlobals globals (SeqNil ty) = mapStep (SeqNil) (stepWithGlobals globals ty)
  stepWithGlobals globals (SeqCons ty head tail) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (SeqCons next head tail))
      Nothing => do
        reduced <- stepWithGlobals globals head
        case reduced of
          Just next => pure (Just (SeqCons ty next tail))
          Nothing => mapStep (SeqCons ty head) (stepWithGlobals globals tail)
  stepWithGlobals globals (SeqCase motive (SeqNil _) base cons) = pure (Just base)
  stepWithGlobals globals (SeqCase motive (SeqCons _ head tail) base cons) = pure (Just (Apply (Apply cons head) tail))
  stepWithGlobals globals (SeqCase motive value base cons) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (SeqCase p value base cons))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just x => pure (Just (SeqCase motive x base cons))
          Nothing => do
            reduced <- stepWithGlobals globals base
            case reduced of
              Just z => pure (Just (SeqCase motive value z cons))
              Nothing => mapStep (SeqCase motive value base) (stepWithGlobals globals cons)
  stepWithGlobals globals (SeqFold motive base next (SeqNil _)) = pure (Just base)
  stepWithGlobals globals (SeqFold motive base next (SeqCons _ head tail)) =
    pure (Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail)))
  stepWithGlobals globals (SeqFold motive base next value) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just p => pure (Just (SeqFold p base next value))
      Nothing => do
        reduced <- stepWithGlobals globals base
        case reduced of
          Just z => pure (Just (SeqFold motive z next value))
          Nothing => do
            reduced <- stepWithGlobals globals next
            case reduced of
              Just s => pure (Just (SeqFold motive base s value))
              Nothing => mapStep (SeqFold motive base next) (stepWithGlobals globals value)
  stepWithGlobals globals (IterateBinary stateType resultType count next initial) = do
    reduced <- stepWithGlobals globals stateType
    case reduced of
      Just x => pure (Just (IterateBinary x resultType count next initial))
      Nothing => do
        reduced <- stepWithGlobals globals resultType
        case reduced of
          Just x => pure (Just (IterateBinary stateType x count next initial))
          Nothing => do
            reduced <- stepWithGlobals globals count
            case reduced of
              Just x => pure (Just (IterateBinary stateType resultType x next initial))
              Nothing => do
                reduced <- stepWithGlobals globals next
                case reduced of
                  Just x => pure (Just (IterateBinary stateType resultType count x initial))
                  Nothing => mapStep (IterateBinary stateType resultType count next) (stepWithGlobals globals initial)
  stepWithGlobals globals (ReadBytes x) = mapStep ReadBytes (stepWithGlobals globals x)
  stepWithGlobals globals (WriteBytes x) = mapStep WriteBytes (stepWithGlobals globals x)
  stepWithGlobals globals RejectBytes = pure Nothing
  stepWithGlobals globals FlushBytes = pure Nothing
  stepWithGlobals globals ReadLine = pure Nothing
  stepWithGlobals globals (FileHandleValue _ _) = pure Nothing
  stepWithGlobals globals (ReadInputFile handle) = mapStep ReadInputFile (stepWithGlobals globals handle)
  stepWithGlobals globals (BytesLengthIs a b) = do
    reduced <- contractLengthIsWith a b
    case reduced of
      Just result => pure (Just result)
      Nothing => do
        reduced <- stepWithGlobals globals a
        case reduced of
          Just next => pure (Just (BytesLengthIs next b))
          Nothing => mapStep (BytesLengthIs a) (stepWithGlobals globals b)
  stepWithGlobals globals (BytesIndex a b) = do
    reduced <- contractIndexWith a b
    case reduced of
      Just result => pure (Just result)
      Nothing => do
        reduced <- stepWithGlobals globals a
        case reduced of
          Just next => pure (Just (BytesIndex next b))
          Nothing => mapStep (BytesIndex a) (stepWithGlobals globals b)
  stepWithGlobals globals (BytesSlice a b c) = do
    reduced <- contractSliceWith a b c
    case reduced of
      Just result => pure (Just result)
      Nothing => do
        reduced <- stepWithGlobals globals a
        case reduced of
          Just next => pure (Just (BytesSlice next b c))
          Nothing => do
            reduced <- stepWithGlobals globals b
            case reduced of
              Just next => pure (Just (BytesSlice a next c))
              Nothing => mapStep (BytesSlice a b) (stepWithGlobals globals c)
  stepWithGlobals globals (UTF8Encode (StringValue text)) = pure (Just (encodeUTF8Value text))
  stepWithGlobals globals (UTF8Encode x) = mapStep UTF8Encode (stepWithGlobals globals x)
  stepWithGlobals globals (UTF8Decode (BytesValue bytes)) = pure (Just (decodeUTF8Value bytes))
  stepWithGlobals globals (UTF8Decode x) = mapStep UTF8Decode (stepWithGlobals globals x)
  stepWithGlobals globals BytesType = pure Nothing
  stepWithGlobals globals (BytesValue _) = pure Nothing
  -- Pure semantics: the region is a fresh erased type; the native runtime also frees a sub-arena.
  stepWithGlobals globals (WithRegion _ body) = pure (Just (Apply body UnitType))
  stepWithGlobals globals (BytesAppend (BytesValue a) (BytesValue b)) = pure (Just (BytesValue (append a b)))
  stepWithGlobals globals (BytesAppend a b) = do
    reduced <- stepWithGlobals globals a
    case reduced of
      Just next => pure (Just (BytesAppend next b))
      Nothing => mapStep (BytesAppend a) (stepWithGlobals globals b)
  stepWithGlobals globals (BytesShare (BytesValue value)) = pure (Just (BoxValue (BoxType Unrestricted BytesType) (BytesValue value)))
  stepWithGlobals globals (BytesShare x) = mapStep BytesShare (stepWithGlobals globals x)
  stepWithGlobals globals (BytesLength (BytesValue value)) = map Just (materializeNatural (byteLength value))
  stepWithGlobals globals (BytesLength x) = mapStep BytesLength (stepWithGlobals globals x)
  stepWithGlobals globals (BytesOctet x) = do
    reduced <- octetOperand x
    case reduced of
      Just byte => pure (Just (BytesValue (fromList [byte])))
      Nothing => mapStep BytesOctet (stepWithGlobals globals x)
  stepWithGlobals globals StringType = pure Nothing
  stepWithGlobals globals (StringValue _) = pure Nothing
  stepWithGlobals globals (StringAppend (StringValue left) (StringValue right)) = pure (Just (StringValue (left ++ right)))
  stepWithGlobals globals (StringAppend left right) = do
    reduced <- stepWithGlobals globals left
    case reduced of
      Just next => pure (Just (StringAppend next right))
      Nothing => mapStep (StringAppend left) (stepWithGlobals globals right)
  stepWithGlobals globals (StringEqual (StringValue left) (StringValue right)) = pure (Just (if left == right then BoolTrue else BoolFalse))
  stepWithGlobals globals (StringEqual left right) = do
    reduced <- stepWithGlobals globals left
    case reduced of
      Just next => pure (Just (StringEqual next right))
      Nothing => mapStep (StringEqual left) (stepWithGlobals globals right)
  stepWithGlobals globals (Prim op args) =
    case evalPrim op args of
      Just value => pure (Just value)
      Nothing => mapStep (Prim op) (stepTermsWithGlobals globals args)
  stepWithGlobals globals (NominalType key indices shape) = do
    reduced <- stepTermsWithGlobals globals indices
    case reduced of
      Just next => pure (Just (NominalType key next shape))
      Nothing => mapStep (NominalType key indices) (stepWithGlobals globals shape)
  stepWithGlobals globals (NominalValue ty value) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (NominalValue next value))
      Nothing => mapStep (NominalValue ty) (stepWithGlobals globals value)
  stepWithGlobals globals (NominalCase motive (NominalValue ty value) branch) = pure (Just (Apply branch value))
  stepWithGlobals globals (NominalCase motive value branch) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just next => pure (Just (NominalCase next value branch))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just next => pure (Just (NominalCase motive next branch))
          Nothing => mapStep (NominalCase motive value) (stepWithGlobals globals branch)
  stepWithGlobals globals (VariantType arms) = mapStep VariantType (stepArmsWithGlobals globals arms)
  stepWithGlobals globals (VariantValue ty tag payload) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (VariantValue next tag payload))
      Nothing => case payload of
        Nothing => pure Nothing
        Just value => mapStep (\next => VariantValue ty tag (Just next)) (stepWithGlobals globals value)
  stepWithGlobals globals (VariantCase motive value branches) =
    case value of
      VariantValue _ tag payload => case variantContract tag payload branches of
        Just result => pure (Just result)
        Nothing => stepVariantCaseWithGlobals globals motive value branches
      _ => stepVariantCaseWithGlobals globals motive value branches
  stepWithGlobals globals (DataType key) = pure Nothing
  stepWithGlobals globals (DataCon key index leading) = pure Nothing
  stepWithGlobals globals (DataCase key motive value branches) =
    case dataContract key value branches of
      Just result => pure (Just result)
      Nothing => stepDataCaseWithGlobals globals key motive value branches
  stepWithGlobals globals (BoxType q ty) = mapStep (BoxType q) (stepWithGlobals globals ty)
  stepWithGlobals globals (BoxValue ty value) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (BoxValue next value))
      Nothing => mapStep (BoxValue ty) (stepWithGlobals globals value)
  stepWithGlobals globals (BoxCase motive (BoxValue ty value) branch) = pure (Just (Apply branch value))
  stepWithGlobals globals (BoxCase motive value branch) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just next => pure (Just (BoxCase next value branch))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just next => pure (Just (BoxCase motive next branch))
          Nothing => mapStep (BoxCase motive value) (stepWithGlobals globals branch)
  stepWithGlobals globals (WithInputFile result path body) = do
    reduced <- stepWithGlobals globals result
    case reduced of
      Just next => pure (Just (WithInputFile next path body))
      Nothing => do
        reduced <- stepWithGlobals globals path
        case reduced of
          Just next => pure (Just (WithInputFile result next body))
          Nothing => mapStep (WithInputFile result path) (stepWithGlobals globals body)
  stepWithGlobals globals (IOType ty) = mapStep IOType (stepWithGlobals globals ty)
  stepWithGlobals globals (FileHandleType region) = mapStep FileHandleType (stepWithGlobals globals region)
  stepWithGlobals globals (IOPure value) = mapStep IOPure (stepWithGlobals globals value)
  stepWithGlobals globals (WriteLine text) = mapStep WriteLine (stepWithGlobals globals text)
  stepWithGlobals globals (IOBind a b (IOPure value) next) = pure (Just (Apply next value))
  stepWithGlobals globals (IOBind a b action next) = do
    reduced <- stepWithGlobals globals a
    case reduced of
      Just result => pure (Just (IOBind result b action next))
      Nothing => do
        reduced <- stepWithGlobals globals b
        case reduced of
          Just result => pure (Just (IOBind a result action next))
          Nothing => do
            reduced <- stepWithGlobals globals action
            case reduced of
              Just result => pure (Just (IOBind a b result next))
              Nothing => mapStep (IOBind a b action) (stepWithGlobals globals next)
  stepWithGlobals globals (BoolCase BoolTrue yes no) = pure (Just yes)
  stepWithGlobals globals (BoolCase BoolFalse yes no) = pure (Just no)
  stepWithGlobals globals (BoolCase condition yes no) = do
    reduced <- stepWithGlobals globals condition
    case reduced of
      Just next => pure (Just (BoolCase next yes no))
      Nothing => do
        reduced <- stepWithGlobals globals yes
        case reduced of
          Just next => pure (Just (BoolCase condition next no))
          Nothing => mapStep (BoolCase condition yes) (stepWithGlobals globals no)
  stepWithGlobals globals (Sigma q r domain body) = do
    reduced <- stepWithGlobals globals domain
    case reduced of
      Just next => pure (Just (Sigma q r next body))
      Nothing => mapStep (Sigma q r domain) (stepWithGlobals globals body)
  stepWithGlobals globals (PairCase motive (PairValue ty first second) branch) = pure (Just (Apply (Apply branch first) second))
  stepWithGlobals globals (PairCase motive scrutinee branch) = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just next => pure (Just (PairCase next scrutinee branch))
      Nothing => do
        reduced <- stepWithGlobals globals scrutinee
        case reduced of
          Just next => pure (Just (PairCase motive next branch))
          Nothing => mapStep (PairCase motive scrutinee) (stepWithGlobals globals branch)
  stepWithGlobals globals (PairValue ty first second) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (PairValue next first second))
      Nothing => do
        reduced <- stepWithGlobals globals first
        case reduced of
          Just next => pure (Just (PairValue ty next second))
          Nothing => mapStep (PairValue ty first) (stepWithGlobals globals second)
  stepWithGlobals globals (Pi q domain body) = do
    reduced <- stepWithGlobals globals domain
    case reduced of
      Just next => pure (Just (Pi q next body))
      Nothing => mapStep (Pi q domain) (stepWithGlobals globals body)
  stepWithGlobals globals (Lambda q domain body) = do
    reduced <- stepWithGlobals globals domain
    case reduced of
      Just next => pure (Just (Lambda q next body))
      Nothing => mapStep (Lambda q domain) (stepWithGlobals globals body)
  -- Fix is neutral for conversion: only its subterms are normalized, never unfolded.
  stepWithGlobals globals (Fix ty body) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (Fix next body))
      Nothing => mapStep (Fix ty) (stepWithGlobals globals body)
  stepWithGlobals globals (Apply (Lambda q domain body) argument) =
    pure (Just (instantiateTerm argument body))
  stepWithGlobals globals (Apply function argument) = do
    reduced <- stepWithGlobals globals function
    case reduced of
      Just next => pure (Just (Apply next argument))
      Nothing => mapStep (Apply function) (stepWithGlobals globals argument)

  stepWithGlobals globals (UnitCase UnitValue body) = pure (Just body)
  stepWithGlobals globals (UnitCase scrutinee body) = do
    reduced <- stepWithGlobals globals scrutinee
    case reduced of
      Just next => pure (Just (UnitCase next body))
      Nothing => mapStep (UnitCase scrutinee) (stepWithGlobals globals body)


  stepVariantCaseWithGlobals : NaturalWork m => (Nat -> Maybe (Term 0)) -> Term n -> Term n -> List (Term n) -> m (Maybe (Term n))
  stepVariantCaseWithGlobals globals motive value branches = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just next => pure (Just (VariantCase next value branches))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just next => pure (Just (VariantCase motive next branches))
          Nothing => mapStep (VariantCase motive value) (stepTermsWithGlobals globals branches)

  stepDataCaseWithGlobals : NaturalWork m => (Nat -> Maybe (Term 0)) -> String -> Term n -> Term n -> List (Term n) -> m (Maybe (Term n))
  stepDataCaseWithGlobals globals key motive value branches = do
    reduced <- stepWithGlobals globals motive
    case reduced of
      Just next => pure (Just (DataCase key next value branches))
      Nothing => do
        reduced <- stepWithGlobals globals value
        case reduced of
          Just next => pure (Just (DataCase key motive next branches))
          Nothing => mapStep (DataCase key motive value) (stepTermsWithGlobals globals branches)

  public export
  stepTermsWithGlobals : NaturalWork m => (Nat -> Maybe (Term 0)) -> List (Term n) -> m (Maybe (List (Term n)))
  stepTermsWithGlobals globals [] = pure Nothing
  stepTermsWithGlobals globals (x :: xs) = do
    reduced <- stepWithGlobals globals x
    case reduced of
      Just next => pure (Just (next :: xs))
      Nothing => mapStep (x ::) (stepTermsWithGlobals globals xs)

  stepArmsWithGlobals : NaturalWork m => (Nat -> Maybe (Term 0)) -> List (Maybe (Quantity, Term n)) -> m (Maybe (List (Maybe (Quantity, Term n))))
  stepArmsWithGlobals globals [] = pure Nothing
  stepArmsWithGlobals globals (Nothing :: rest) = mapStep (Nothing ::) (stepArmsWithGlobals globals rest)
  stepArmsWithGlobals globals (Just (q, ty) :: rest) = do
    reduced <- stepWithGlobals globals ty
    case reduced of
      Just next => pure (Just (Just (q, next) :: rest))
      Nothing => mapStep (Just (q, ty) ::) (stepArmsWithGlobals globals rest)


||| Existing unmetered full reduction, with unchanged selection/demand order.
public export
step : Term n -> Maybe (Term n)
step term = runIdentity (stepWithGlobals (const Nothing) term)

||| Global unfolding is one ordinary reduction contraction; callers supply a
||| validated acyclic environment when using this for typing or execution.
public export
stepGlobals : (Nat -> Maybe (Term 0)) -> Term n -> Maybe (Term n)
stepGlobals globals term = runIdentity (stepWithGlobals globals term)

||| Compatibility entry point: closed syntax has no global environment.
public export
stepWith : NaturalWork m => Term n -> m (Maybe (Term n))
stepWith = stepWithGlobals (const Nothing)

||| Bounded reduction either reaches a normal form or retains unfinished syntax.
public export
data ReductionResult : Nat -> Type where
  Normal : Term n -> ReductionResult n
  OutOfFuel : Term n -> ReductionResult n

||| Fuel bounds beta/data-case contractions, not time, allocation, or term size.
||| Even at zero fuel, a normal input is recognized by inspecting its next step.
public export
normalize : Nat -> Term n -> ReductionResult n
normalize fuel term =
  case step term of
    Nothing => Normal term
    Just next =>
      case fuel of
        Z => OutOfFuel term
        S rest => normalize rest next

||| Reference beta/data-case conversion outcome; no eta or cubical conversion is included.
public export
data ConversionResult = EqualNormalForms | DifferentNormalForms | Inconclusive

||| Normalize each input with its own budget; exhaustion never means inequality.
||| This is not yet the language's definitional equality judgment.
public export
betaCompare : Nat -> Term n -> Term n -> ConversionResult
betaCompare fuel left right =
  case (normalize fuel left, normalize fuel right) of
    (Normal x, Normal y) =>
      if sameSyntax x y then EqualNormalForms else DifferentNormalForms
    _ => Inconclusive

||| Environment-aware conversion, with explicit exhaustion for unfolding too.
public export
normalizeGlobals : (Nat -> Maybe (Term 0)) -> Nat -> Term n -> ReductionResult n
normalizeGlobals globals fuel term =
  case stepGlobals globals term of
    Nothing => Normal term
    Just next => case fuel of
      Z => OutOfFuel term
      S rest => normalizeGlobals globals rest next

||| Environment-aware comparison; both sides use the same immutable environment.
public export
betaCompareGlobals : (Nat -> Maybe (Term 0)) -> Nat -> Term n -> Term n -> ConversionResult
betaCompareGlobals globals fuel left right =
  case (normalizeGlobals globals fuel left, normalizeGlobals globals fuel right) of
    (Normal x, Normal y) => if sameSyntax x y then EqualNormalForms else DifferentNormalForms
    _ => Inconclusive
