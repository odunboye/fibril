-- Reference beta/data-case reduction for ordinary scoped syntax, not a typed evaluator.
-- Binding background: DEBRUIJN72; see docs/references.md and docs/reduction.md.
module Fibril.Core.Reduction

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

mutual
  ||| One leftmost full beta/data-case step, including domain annotations and binder bodies.
  ||| Nothing means reference normal form for this grammar, not well typed or valid.
  public export
  step : Term n -> Maybe (Term n)
  step (Variable i) = Nothing
  step (Universe l) = Nothing
  step UnitType = Nothing
  step UnitValue = Nothing
  step BoolType = Nothing
  step BoolTrue = Nothing
  step BoolFalse = Nothing
  step NatType = Nothing
  step NatZero = Nothing
  step (NatSucc value) = map NatSucc (step value)
  step (NatRec motive base next NatZero) = Just base
  step (NatRec motive base next (NatSucc value)) =
    Just (Apply (Apply next value) (NatRec motive base next value))
  step (NatRec motive base next value) = case step motive of
    Just p => Just (NatRec p base next value)
    Nothing => case step base of
      Just z => Just (NatRec motive z next value)
      Nothing => case step next of
        Just s => Just (NatRec motive base s value)
        Nothing => map (NatRec motive base next) (step value)
  step (NatRecRuntime motive base next NatZero) = Just base
  step (NatRecRuntime motive base next (NatSucc value)) =
    Just (Apply (Apply next value) (NatRecRuntime motive base next value))
  step (NatRecRuntime motive base next value) = case step motive of
    Just p => Just (NatRecRuntime p base next value)
    Nothing => case step base of
      Just z => Just (NatRecRuntime motive z next value)
      Nothing => case step next of
        Just s => Just (NatRecRuntime motive base s value)
        Nothing => map (NatRecRuntime motive base next) (step value)
  step (RecType _) = Nothing
  step (RecEnd ty) = RecEnd <$> step ty
  step (RecMore ty tail) = case step ty of
    Just next => Just (RecMore next tail)
    Nothing => RecMore ty <$> step tail
  step (RecFold motive base next (RecEnd _)) = Just base
  step (RecFold motive base next (RecMore _ tail)) =
    Just (Apply (Apply next tail) (RecFold motive base next tail))
  step (RecFold motive base next value) = case step motive of
    Just p => Just (RecFold p base next value)
    Nothing => case step base of
      Just z => Just (RecFold motive z next value)
      Nothing => case step next of
        Just s => Just (RecFold motive base s value)
        Nothing => RecFold motive base next <$> step value
  step (RecCase motive (RecEnd _) base more) = Just base
  step (RecCase motive (RecMore _ tail) base more) = Just (Apply more tail)
  step (RecCase motive value base more) = case step motive of
    Just p => Just (RecCase p value base more)
    Nothing => case step value of
      Just x => Just (RecCase motive x base more)
      Nothing => case step base of
        Just z => Just (RecCase motive value z more)
        Nothing => RecCase motive value base <$> step more
  step (SeqType key element) = SeqType key <$> step element
  step (SeqNil ty) = SeqNil <$> step ty
  step (SeqCons ty head tail) = case step ty of
    Just next => Just (SeqCons next head tail)
    Nothing => case step head of
      Just next => Just (SeqCons ty next tail)
      Nothing => SeqCons ty head <$> step tail
  step (SeqCase motive (SeqNil _) base cons) = Just base
  step (SeqCase motive (SeqCons _ head tail) base cons) = Just (Apply (Apply cons head) tail)
  step (SeqCase motive value base cons) = case step motive of
    Just p => Just (SeqCase p value base cons)
    Nothing => case step value of
      Just x => Just (SeqCase motive x base cons)
      Nothing => case step base of
        Just z => Just (SeqCase motive value z cons)
        Nothing => SeqCase motive value base <$> step cons
  step (SeqFold motive base next (SeqNil _)) = Just base
  step (SeqFold motive base next (SeqCons _ head tail)) =
    Just (Apply (Apply (Apply next head) tail) (SeqFold motive base next tail))
  step (SeqFold motive base next value) = case step motive of
    Just p => Just (SeqFold p base next value)
    Nothing => case step base of
      Just z => Just (SeqFold motive z next value)
      Nothing => case step next of
        Just s => Just (SeqFold motive base s value)
        Nothing => SeqFold motive base next <$> step value
  step (ReadBytes x) = map ReadBytes (step x)
  step (WriteBytes x) = map WriteBytes (step x)
  step FlushBytes = Nothing
  step ReadLine = Nothing
  step (FileHandleValue _ _) = Nothing
  step (ReadInputFile handle) = map ReadInputFile (step handle)
  step (BytesIndex a b) = case contractBytesIndex a b of
    Just result => Just result
    Nothing => case step a of
      Just next => Just (BytesIndex next b)
      Nothing => map (BytesIndex a) (step b)
  step (BytesSlice a b c) = case contractBytesSlice a b c of
    Just result => Just result
    Nothing => case step a of
      Just next => Just (BytesSlice next b c)
      Nothing => case step b of
        Just next => Just (BytesSlice a next c)
        Nothing => map (BytesSlice a b) (step c)
  step (UTF8Encode (StringValue text)) = Just (encodeUTF8Value text)
  step (UTF8Encode x) = map UTF8Encode (step x)
  step (UTF8Decode (BytesValue bytes)) = Just (decodeUTF8Value bytes)
  step (UTF8Decode x) = map UTF8Decode (step x)
  step BytesType = Nothing
  step (BytesValue _) = Nothing
  step (BytesAppend (BytesValue a) (BytesValue b)) = Just (BytesValue (append a b))
  step (BytesAppend a b) = case step a of
    Just next => Just (BytesAppend next b)
    Nothing => map (BytesAppend a) (step b)
  step (BytesLength (BytesValue value)) = Just (naturalTerm (byteLength value))
  step (BytesLength x) = map BytesLength (step x)
  step (BytesOctet x) = case canonicalOctet x of
    Just byte => Just (BytesValue (fromList [byte]))
    Nothing => map BytesOctet (step x)
  step StringType = Nothing
  step (StringValue _) = Nothing
  step (StringAppend (StringValue left) (StringValue right)) = Just (StringValue (left ++ right))
  step (StringAppend left right) = case step left of
    Just next => Just (StringAppend next right)
    Nothing => map (StringAppend left) (step right)
  step (StringEqual (StringValue left) (StringValue right)) = Just (if left == right then BoolTrue else BoolFalse)
  step (StringEqual left right) = case step left of
    Just next => Just (StringEqual next right)
    Nothing => map (StringEqual left) (step right)
  step (NominalType key indices shape) = case stepTerms indices of
    Just next => Just (NominalType key next shape)
    Nothing => map (NominalType key indices) (step shape)
  step (NominalValue ty value) = case step ty of
    Just next => Just (NominalValue next value)
    Nothing => map (NominalValue ty) (step value)
  step (NominalCase motive (NominalValue ty value) branch) = Just (Apply branch value)
  step (NominalCase motive value branch) = case step motive of
    Just next => Just (NominalCase next value branch)
    Nothing => case step value of
      Just next => Just (NominalCase motive next branch)
      Nothing => map (NominalCase motive value) (step branch)
  step (VariantType arms) = map VariantType (stepArms arms)
  step (VariantValue ty tag payload) = case step ty of
    Just next => Just (VariantValue next tag payload)
    Nothing => case payload of
      Nothing => Nothing
      Just value => map (\next => VariantValue ty tag (Just next)) (step value)
  step (VariantCase motive value branches) =
    case value of
      VariantValue _ tag payload => case variantContract tag payload branches of
        Just result => Just result
        Nothing => stepVariantCase motive value branches
      _ => stepVariantCase motive value branches
  step (BoxType q ty) = map (BoxType q) (step ty)
  step (BoxValue ty value) = case step ty of
    Just next => Just (BoxValue next value)
    Nothing => map (BoxValue ty) (step value)
  step (BoxCase motive (BoxValue ty value) branch) = Just (Apply branch value)
  step (BoxCase motive value branch) = case step motive of
    Just next => Just (BoxCase next value branch)
    Nothing => case step value of
      Just next => Just (BoxCase motive next branch)
      Nothing => map (BoxCase motive value) (step branch)
  step (WithInputFile result path body) = case step result of
    Just next => Just (WithInputFile next path body)
    Nothing => case step path of
      Just next => Just (WithInputFile result next body)
      Nothing => map (WithInputFile result path) (step body)
  step (IOType ty) = map IOType (step ty)
  step (FileHandleType region) = map FileHandleType (step region)
  step (IOPure value) = map IOPure (step value)
  step (WriteLine text) = map WriteLine (step text)
  step (IOBind a b (IOPure value) next) = Just (Apply next value)
  step (IOBind a b action next) =
    case step a of
      Just result => Just (IOBind result b action next)
      Nothing => case step b of
        Just result => Just (IOBind a result action next)
        Nothing => case step action of
          Just result => Just (IOBind a b result next)
          Nothing => map (IOBind a b action) (step next)
  step (BoolCase BoolTrue yes no) = Just yes
  step (BoolCase BoolFalse yes no) = Just no
  step (BoolCase condition yes no) =
    case step condition of
      Just next => Just (BoolCase next yes no)
      Nothing => case step yes of
        Just next => Just (BoolCase condition next no)
        Nothing => map (BoolCase condition yes) (step no)
  step (Sigma q r domain body) =
    case step domain of
      Just next => Just (Sigma q r next body)
      Nothing => map (Sigma q r domain) (step body)
  step (PairCase motive (PairValue ty first second) branch) = Just (Apply (Apply branch first) second)
  step (PairCase motive scrutinee branch) =
    case step motive of
      Just next => Just (PairCase next scrutinee branch)
      Nothing => case step scrutinee of
        Just next => Just (PairCase motive next branch)
        Nothing => map (PairCase motive scrutinee) (step branch)
  step (PairValue ty first second) =
    case step ty of
      Just next => Just (PairValue next first second)
      Nothing => case step first of
        Just next => Just (PairValue ty next second)
        Nothing => map (PairValue ty first) (step second)
  step (Pi q domain body) =
    case step domain of
      Just next => Just (Pi q next body)
      Nothing => map (Pi q domain) (step body)
  step (Lambda q domain body) =
    case step domain of
      Just next => Just (Lambda q next body)
      Nothing => map (Lambda q domain) (step body)
  step (Apply (Lambda q domain body) argument) =
    Just (instantiateTerm argument body)
  step (Apply function argument) =
    case step function of
      Just next => Just (Apply next argument)
      Nothing => map (Apply function) (step argument)

  step (UnitCase UnitValue body) = Just body
  step (UnitCase scrutinee body) =
    case step scrutinee of
      Just next => Just (UnitCase next body)
      Nothing => map (UnitCase scrutinee) (step body)


  stepVariantCase : Term n -> Term n -> List (Term n) -> Maybe (Term n)
  stepVariantCase motive value branches = case step motive of
    Just next => Just (VariantCase next value branches)
    Nothing => case step value of
      Just next => Just (VariantCase motive next branches)
      Nothing => map (VariantCase motive value) (stepTerms branches)

  stepTerms : List (Term n) -> Maybe (List (Term n))
  stepTerms [] = Nothing
  stepTerms (x :: xs) = case step x of
    Just next => Just (next :: xs)
    Nothing => map (x ::) (stepTerms xs)

  stepArms : List (Maybe (Quantity, Term n)) -> Maybe (List (Maybe (Quantity, Term n)))
  stepArms [] = Nothing
  stepArms (Nothing :: rest) = map (Nothing ::) (stepArms rest)
  stepArms (Just (q, ty) :: rest) = case step ty of
    Just next => Just (Just (q, next) :: rest)
    Nothing => map (Just (q, ty) ::) (stepArms rest)


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
