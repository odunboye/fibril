-- Reference beta/data-case reduction for ordinary scoped syntax, not a typed evaluator.
-- Binding background: DEBRUIJN72; see docs/references.md and docs/reduction.md.
module Fibril.Core.Reduction

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

-- Lift the existing Maybe step result through the chosen work policy.
mapStep : Functor m => (a -> b) -> m (Maybe a) -> m (Maybe b)
mapStep f = map (map f)

mutual
  ||| One leftmost full beta/data-case step, including domain annotations and binder bodies.
  ||| Nothing means reference normal form for this grammar, not well typed or valid.
  public export
  stepWith : NaturalWork m => Term n -> m (Maybe (Term n))
  stepWith (Variable i) = pure Nothing
  stepWith (Universe l) = pure Nothing
  stepWith UnitType = pure Nothing
  stepWith UnitValue = pure Nothing
  stepWith BoolType = pure Nothing
  stepWith BoolTrue = pure Nothing
  stepWith BoolFalse = pure Nothing
  stepWith NatType = pure Nothing
  stepWith NatZero = pure Nothing
  stepWith (NatSucc value) = do
    visitSuccessor
    mapStep NatSucc (stepWith value)
  stepWith (NatRec motive base next NatZero) = pure (Just base)
  stepWith (NatRec motive base next (NatSucc value)) = do
    visitSuccessor
    pure (Just (Apply (Apply next value) (NatRec motive base next value)))
  stepWith (NatRec motive base next value) = do
    reduced <- stepWith motive
    case reduced of
      Just p => pure (Just (NatRec p base next value))
      Nothing => do
        reduced <- stepWith base
        case reduced of
          Just z => pure (Just (NatRec motive z next value))
          Nothing => do
            reduced <- stepWith next
            case reduced of
              Just s => pure (Just (NatRec motive base s value))
              Nothing => mapStep (NatRec motive base next) (stepWith value)
  stepWith (NatRecRuntime motive base next NatZero) = pure (Just base)
  stepWith (NatRecRuntime motive base next (NatSucc value)) = do
    visitSuccessor
    pure (Just (Apply (Apply next value) (NatRecRuntime motive base next value)))
  stepWith (NatRecRuntime motive base next value) = do
    reduced <- stepWith motive
    case reduced of
      Just p => pure (Just (NatRecRuntime p base next value))
      Nothing => do
        reduced <- stepWith base
        case reduced of
          Just z => pure (Just (NatRecRuntime motive z next value))
          Nothing => do
            reduced <- stepWith next
            case reduced of
              Just s => pure (Just (NatRecRuntime motive base s value))
              Nothing => mapStep (NatRecRuntime motive base next) (stepWith value)
  stepWith (RecType _) = pure Nothing
  stepWith (RecEnd ty) = mapStep RecEnd (stepWith ty)
  stepWith (RecMore ty tail) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (RecMore next tail))
      Nothing => mapStep (RecMore ty) (stepWith tail)
  stepWith (RecFold motive base next (RecEnd _)) = pure (Just base)
  stepWith (RecFold motive base next (RecMore _ tail)) =
    pure (Just (Apply (Apply next tail) (RecFold motive base next tail)))
  stepWith (RecFold motive base next value) = do
    reduced <- stepWith motive
    case reduced of
      Just p => pure (Just (RecFold p base next value))
      Nothing => do
        reduced <- stepWith base
        case reduced of
          Just z => pure (Just (RecFold motive z next value))
          Nothing => do
            reduced <- stepWith next
            case reduced of
              Just s => pure (Just (RecFold motive base s value))
              Nothing => mapStep (RecFold motive base next) (stepWith value)
  stepWith (RecCase motive (RecEnd _) base more) = pure (Just base)
  stepWith (RecCase motive (RecMore _ tail) base more) = pure (Just (Apply more tail))
  stepWith (RecCase motive value base more) = do
    reduced <- stepWith motive
    case reduced of
      Just p => pure (Just (RecCase p value base more))
      Nothing => do
        reduced <- stepWith value
        case reduced of
          Just x => pure (Just (RecCase motive x base more))
          Nothing => do
            reduced <- stepWith base
            case reduced of
              Just z => pure (Just (RecCase motive value z more))
              Nothing => mapStep (RecCase motive value base) (stepWith more)
  stepWith (SeqType key element) = mapStep (SeqType key) (stepWith element)
  stepWith (SeqNil ty) = mapStep (SeqNil) (stepWith ty)
  stepWith (SeqCons ty head tail) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (SeqCons next head tail))
      Nothing => do
        reduced <- stepWith head
        case reduced of
          Just next => pure (Just (SeqCons ty next tail))
          Nothing => mapStep (SeqCons ty head) (stepWith tail)
  stepWith (SeqCase motive (SeqNil _) base cons) = pure (Just base)
  stepWith (SeqCase motive (SeqCons _ head tail) base cons) = pure (Just (Apply (Apply cons head) tail))
  stepWith (SeqCase motive value base cons) = do
    reduced <- stepWith motive
    case reduced of
      Just p => pure (Just (SeqCase p value base cons))
      Nothing => do
        reduced <- stepWith value
        case reduced of
          Just x => pure (Just (SeqCase motive x base cons))
          Nothing => do
            reduced <- stepWith base
            case reduced of
              Just z => pure (Just (SeqCase motive value z cons))
              Nothing => mapStep (SeqCase motive value base) (stepWith cons)
  stepWith (SeqFold motive base next (SeqNil _)) = pure (Just base)
  stepWith (SeqFold motive base next (SeqCons _ head tail)) =
    pure (Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail)))
  stepWith (SeqFold motive base next value) = do
    reduced <- stepWith motive
    case reduced of
      Just p => pure (Just (SeqFold p base next value))
      Nothing => do
        reduced <- stepWith base
        case reduced of
          Just z => pure (Just (SeqFold motive z next value))
          Nothing => do
            reduced <- stepWith next
            case reduced of
              Just s => pure (Just (SeqFold motive base s value))
              Nothing => mapStep (SeqFold motive base next) (stepWith value)
  stepWith (IterateBinary stateType resultType count next initial) = do
    reduced <- stepWith stateType
    case reduced of
      Just x => pure (Just (IterateBinary x resultType count next initial))
      Nothing => do
        reduced <- stepWith resultType
        case reduced of
          Just x => pure (Just (IterateBinary stateType x count next initial))
          Nothing => do
            reduced <- stepWith count
            case reduced of
              Just x => pure (Just (IterateBinary stateType resultType x next initial))
              Nothing => do
                reduced <- stepWith next
                case reduced of
                  Just x => pure (Just (IterateBinary stateType resultType count x initial))
                  Nothing => mapStep (IterateBinary stateType resultType count next) (stepWith initial)
  stepWith (ReadBytes x) = mapStep ReadBytes (stepWith x)
  stepWith (WriteBytes x) = mapStep WriteBytes (stepWith x)
  stepWith RejectBytes = pure Nothing
  stepWith FlushBytes = pure Nothing
  stepWith ReadLine = pure Nothing
  stepWith (FileHandleValue _ _) = pure Nothing
  stepWith (ReadInputFile handle) = mapStep ReadInputFile (stepWith handle)
  stepWith (BytesLengthIs a b) = do
    reduced <- contractLengthIsWith a b
    case reduced of
      Just result => pure (Just result)
      Nothing => do
        reduced <- stepWith a
        case reduced of
          Just next => pure (Just (BytesLengthIs next b))
          Nothing => mapStep (BytesLengthIs a) (stepWith b)
  stepWith (BytesIndex a b) = do
    reduced <- contractIndexWith a b
    case reduced of
      Just result => pure (Just result)
      Nothing => do
        reduced <- stepWith a
        case reduced of
          Just next => pure (Just (BytesIndex next b))
          Nothing => mapStep (BytesIndex a) (stepWith b)
  stepWith (BytesSlice a b c) = do
    reduced <- contractSliceWith a b c
    case reduced of
      Just result => pure (Just result)
      Nothing => do
        reduced <- stepWith a
        case reduced of
          Just next => pure (Just (BytesSlice next b c))
          Nothing => do
            reduced <- stepWith b
            case reduced of
              Just next => pure (Just (BytesSlice a next c))
              Nothing => mapStep (BytesSlice a b) (stepWith c)
  stepWith (UTF8Encode (StringValue text)) = pure (Just (encodeUTF8Value text))
  stepWith (UTF8Encode x) = mapStep UTF8Encode (stepWith x)
  stepWith (UTF8Decode (BytesValue bytes)) = pure (Just (decodeUTF8Value bytes))
  stepWith (UTF8Decode x) = mapStep UTF8Decode (stepWith x)
  stepWith BytesType = pure Nothing
  stepWith (BytesValue _) = pure Nothing
  stepWith (BytesAppend (BytesValue a) (BytesValue b)) = pure (Just (BytesValue (append a b)))
  stepWith (BytesAppend a b) = do
    reduced <- stepWith a
    case reduced of
      Just next => pure (Just (BytesAppend next b))
      Nothing => mapStep (BytesAppend a) (stepWith b)
  stepWith (BytesShare (BytesValue value)) = pure (Just (BoxValue (BoxType Unrestricted BytesType) (BytesValue value)))
  stepWith (BytesShare x) = mapStep BytesShare (stepWith x)
  stepWith (BytesLength (BytesValue value)) = map Just (materializeNatural (byteLength value))
  stepWith (BytesLength x) = mapStep BytesLength (stepWith x)
  stepWith (BytesOctet x) = do
    reduced <- octetOperand x
    case reduced of
      Just byte => pure (Just (BytesValue (fromList [byte])))
      Nothing => mapStep BytesOctet (stepWith x)
  stepWith StringType = pure Nothing
  stepWith (StringValue _) = pure Nothing
  stepWith (StringAppend (StringValue left) (StringValue right)) = pure (Just (StringValue (left ++ right)))
  stepWith (StringAppend left right) = do
    reduced <- stepWith left
    case reduced of
      Just next => pure (Just (StringAppend next right))
      Nothing => mapStep (StringAppend left) (stepWith right)
  stepWith (StringEqual (StringValue left) (StringValue right)) = pure (Just (if left == right then BoolTrue else BoolFalse))
  stepWith (StringEqual left right) = do
    reduced <- stepWith left
    case reduced of
      Just next => pure (Just (StringEqual next right))
      Nothing => mapStep (StringEqual left) (stepWith right)
  stepWith (NominalType key indices shape) = do
    reduced <- stepTermsWith indices
    case reduced of
      Just next => pure (Just (NominalType key next shape))
      Nothing => mapStep (NominalType key indices) (stepWith shape)
  stepWith (NominalValue ty value) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (NominalValue next value))
      Nothing => mapStep (NominalValue ty) (stepWith value)
  stepWith (NominalCase motive (NominalValue ty value) branch) = pure (Just (Apply branch value))
  stepWith (NominalCase motive value branch) = do
    reduced <- stepWith motive
    case reduced of
      Just next => pure (Just (NominalCase next value branch))
      Nothing => do
        reduced <- stepWith value
        case reduced of
          Just next => pure (Just (NominalCase motive next branch))
          Nothing => mapStep (NominalCase motive value) (stepWith branch)
  stepWith (VariantType arms) = mapStep VariantType (stepArmsWith arms)
  stepWith (VariantValue ty tag payload) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (VariantValue next tag payload))
      Nothing => case payload of
        Nothing => pure Nothing
        Just value => mapStep (\next => VariantValue ty tag (Just next)) (stepWith value)
  stepWith (VariantCase motive value branches) =
    case value of
      VariantValue _ tag payload => case variantContract tag payload branches of
        Just result => pure (Just result)
        Nothing => stepVariantCaseWith motive value branches
      _ => stepVariantCaseWith motive value branches
  stepWith (BoxType q ty) = mapStep (BoxType q) (stepWith ty)
  stepWith (BoxValue ty value) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (BoxValue next value))
      Nothing => mapStep (BoxValue ty) (stepWith value)
  stepWith (BoxCase motive (BoxValue ty value) branch) = pure (Just (Apply branch value))
  stepWith (BoxCase motive value branch) = do
    reduced <- stepWith motive
    case reduced of
      Just next => pure (Just (BoxCase next value branch))
      Nothing => do
        reduced <- stepWith value
        case reduced of
          Just next => pure (Just (BoxCase motive next branch))
          Nothing => mapStep (BoxCase motive value) (stepWith branch)
  stepWith (WithInputFile result path body) = do
    reduced <- stepWith result
    case reduced of
      Just next => pure (Just (WithInputFile next path body))
      Nothing => do
        reduced <- stepWith path
        case reduced of
          Just next => pure (Just (WithInputFile result next body))
          Nothing => mapStep (WithInputFile result path) (stepWith body)
  stepWith (IOType ty) = mapStep IOType (stepWith ty)
  stepWith (FileHandleType region) = mapStep FileHandleType (stepWith region)
  stepWith (IOPure value) = mapStep IOPure (stepWith value)
  stepWith (WriteLine text) = mapStep WriteLine (stepWith text)
  stepWith (IOBind a b (IOPure value) next) = pure (Just (Apply next value))
  stepWith (IOBind a b action next) = do
    reduced <- stepWith a
    case reduced of
      Just result => pure (Just (IOBind result b action next))
      Nothing => do
        reduced <- stepWith b
        case reduced of
          Just result => pure (Just (IOBind a result action next))
          Nothing => do
            reduced <- stepWith action
            case reduced of
              Just result => pure (Just (IOBind a b result next))
              Nothing => mapStep (IOBind a b action) (stepWith next)
  stepWith (BoolCase BoolTrue yes no) = pure (Just yes)
  stepWith (BoolCase BoolFalse yes no) = pure (Just no)
  stepWith (BoolCase condition yes no) = do
    reduced <- stepWith condition
    case reduced of
      Just next => pure (Just (BoolCase next yes no))
      Nothing => do
        reduced <- stepWith yes
        case reduced of
          Just next => pure (Just (BoolCase condition next no))
          Nothing => mapStep (BoolCase condition yes) (stepWith no)
  stepWith (Sigma q r domain body) = do
    reduced <- stepWith domain
    case reduced of
      Just next => pure (Just (Sigma q r next body))
      Nothing => mapStep (Sigma q r domain) (stepWith body)
  stepWith (PairCase motive (PairValue ty first second) branch) = pure (Just (Apply (Apply branch first) second))
  stepWith (PairCase motive scrutinee branch) = do
    reduced <- stepWith motive
    case reduced of
      Just next => pure (Just (PairCase next scrutinee branch))
      Nothing => do
        reduced <- stepWith scrutinee
        case reduced of
          Just next => pure (Just (PairCase motive next branch))
          Nothing => mapStep (PairCase motive scrutinee) (stepWith branch)
  stepWith (PairValue ty first second) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (PairValue next first second))
      Nothing => do
        reduced <- stepWith first
        case reduced of
          Just next => pure (Just (PairValue ty next second))
          Nothing => mapStep (PairValue ty first) (stepWith second)
  stepWith (Pi q domain body) = do
    reduced <- stepWith domain
    case reduced of
      Just next => pure (Just (Pi q next body))
      Nothing => mapStep (Pi q domain) (stepWith body)
  stepWith (Lambda q domain body) = do
    reduced <- stepWith domain
    case reduced of
      Just next => pure (Just (Lambda q next body))
      Nothing => mapStep (Lambda q domain) (stepWith body)
  stepWith (Apply (Lambda q domain body) argument) =
    pure (Just (instantiateTerm argument body))
  stepWith (Apply function argument) = do
    reduced <- stepWith function
    case reduced of
      Just next => pure (Just (Apply next argument))
      Nothing => mapStep (Apply function) (stepWith argument)

  stepWith (UnitCase UnitValue body) = pure (Just body)
  stepWith (UnitCase scrutinee body) = do
    reduced <- stepWith scrutinee
    case reduced of
      Just next => pure (Just (UnitCase next body))
      Nothing => mapStep (UnitCase scrutinee) (stepWith body)


  stepVariantCaseWith : NaturalWork m => Term n -> Term n -> List (Term n) -> m (Maybe (Term n))
  stepVariantCaseWith motive value branches = do
    reduced <- stepWith motive
    case reduced of
      Just next => pure (Just (VariantCase next value branches))
      Nothing => do
        reduced <- stepWith value
        case reduced of
          Just next => pure (Just (VariantCase motive next branches))
          Nothing => mapStep (VariantCase motive value) (stepTermsWith branches)

  stepTermsWith : NaturalWork m => List (Term n) -> m (Maybe (List (Term n)))
  stepTermsWith [] = pure Nothing
  stepTermsWith (x :: xs) = do
    reduced <- stepWith x
    case reduced of
      Just next => pure (Just (next :: xs))
      Nothing => mapStep (x ::) (stepTermsWith xs)

  stepArmsWith : NaturalWork m => List (Maybe (Quantity, Term n)) -> m (Maybe (List (Maybe (Quantity, Term n))))
  stepArmsWith [] = pure Nothing
  stepArmsWith (Nothing :: rest) = mapStep (Nothing ::) (stepArmsWith rest)
  stepArmsWith (Just (q, ty) :: rest) = do
    reduced <- stepWith ty
    case reduced of
      Just next => pure (Just (Just (q, next) :: rest))
      Nothing => mapStep (Just (q, ty) ::) (stepArmsWith rest)


||| Existing unmetered full reduction, with unchanged selection/demand order.
public export
step : Term n -> Maybe (Term n)
step term = runIdentity (stepWith term)

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
