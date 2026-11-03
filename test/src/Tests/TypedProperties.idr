module Tests.TypedProperties

import Data.Fin
import Data.Vect
import Hedgehog
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Erased

%default total

-- A generator-side construction recipe, NOT a kernel-checked proof object.
-- Keeping syntax and type together preserves their relationship while shrinking.
record TypedSample where
  constructor Sample
  term : Term 0
  expected : Term 0

Show TypedSample where
  show (Sample term ty) = renderTerm term ++ " : " ++ renderTerm ty

seed : Gen TypedSample
seed = element
  [ Sample (Sigma Erased Linear (Universe 0) (Variable FZ)) (Universe 1)
  , Sample (PairValue (Sigma Erased Linear (Universe 0) (Variable FZ)) StringType (StringValue "packed"))
           (Sigma Erased Linear (Universe 0) (Variable FZ))
  , Sample (IOType StringType) (Universe 0)
  , Sample (IOPure (StringValue "pure")) (IOType StringType)
  , Sample (WriteLine (StringValue "request")) (IOType UnitType)
  , Sample StringType (Universe 0)
  , Sample (StringValue "") StringType
  , Sample (StringValue "λ 🌍") StringType
  , Sample (StringAppend (StringValue "λ ") (StringValue "🌍")) StringType
  , Sample BoolType (Universe 0)
  , Sample BoolTrue BoolType
  , Sample (StringEqual (StringValue "same") (StringValue "same")) BoolType
  , Sample BoolFalse BoolType
  , Sample UnitType (Universe 0)
  , Sample UnitValue UnitType
  , Sample (Universe 0) (Universe 1)
  , Sample (Universe 1) (Universe 2)
  , Sample
      (Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ)))
      (Pi Erased (Universe 0) (Pi Linear (Variable FZ) (Variable (FS FZ))))
  ]

-- Both constructors preserve erased typing by construction, without invoking
-- the checker as a filter or using inference to manufacture expected answers.
wrapLambda : Quantity -> TypedSample -> TypedSample
wrapLambda q (Sample term ty) =
  Sample (Lambda q (Universe 0) (weaken term))
         (Pi q (Universe 0) (weaken ty))

wrapBeta : Quantity -> TypedSample -> TypedSample
wrapBeta q (Sample term ty) =
  Sample (Apply (Lambda q ty (Variable FZ)) term) ty

typedGen : Nat -> Gen TypedSample
typedGen Z = seed
typedGen (S depth) =
  choice
    [ seed
    , (\sample => let body = VariantType [Just (Linear, sample.expected)]
                      ty = NominalType "Generated.Packet" [sample.expected] body
                    in Sample (NominalValue ty (VariantValue body 0 (Just sample.term))) ty) <$> typedGen depth
    , (\sample => let body = VariantType [Just (Linear, sample.expected)]
                      ty = NominalType "Generated.Packet" [sample.expected] body
                      branch = Lambda Linear body (VariantCase
                        (Lambda Erased (weaken body) (weaken (weaken sample.expected))) (Variable FZ)
                        [Lambda Linear (weaken sample.expected) (Variable FZ)])
                    in Sample (NominalCase (Lambda Erased ty (weaken sample.expected))
                         (NominalValue ty (VariantValue body 0 (Just sample.term))) branch) sample.expected) <$> typedGen depth
    , (\sample => let ty = VariantType [Nothing, Just (Linear, sample.expected)]
                    in Sample (VariantValue ty 1 (Just sample.term)) ty) <$> typedGen depth
    , (\sample => let ty = VariantType [Nothing, Just (Linear, sample.expected)]
                      motive = Lambda Erased ty (weaken sample.expected)
                    in Sample (VariantCase motive (VariantValue ty 1 (Just sample.term))
                         [sample.term, Lambda Linear sample.expected (Variable FZ)]) sample.expected) <$> typedGen depth
    , (\sample => let ty = BoxType Linear sample.expected
                    in Sample (BoxValue ty sample.term) ty) <$> typedGen depth
    , (\sample => let ty = BoxType Linear sample.expected
                      motive = Lambda Erased ty (weaken sample.expected)
                      branch = Lambda Linear sample.expected (Variable FZ)
                    in Sample (BoxCase motive (BoxValue ty sample.term) branch) sample.expected) <$> typedGen depth
    , (\sample => let ty = Sigma Erased Linear UnitType (weaken sample.expected)
                    in Sample (PairValue ty UnitValue sample.term) ty) <$> typedGen depth
    , (\sample => let ty = Sigma Erased Linear UnitType (weaken sample.expected)
                      motive = Lambda Erased ty (weaken sample.expected)
                      branch = Lambda Erased UnitType (Lambda Linear (weaken sample.expected) (Variable FZ))
                    in Sample (PairCase motive (PairValue ty UnitValue sample.term) branch) sample.expected) <$> typedGen depth
    , wrapLambda <$> element [Erased, Linear, Unrestricted] <*> typedGen depth
    , wrapBeta <$> element [Erased, Linear, Unrestricted] <*> typedGen depth
    , (\sample => Sample (UnitCase UnitValue sample.term) sample.expected) <$> typedGen depth
    , (\sample => Sample (BoolCase BoolFalse sample.term (wrapBeta Linear sample).term)
                         sample.expected) <$> typedGen depth
    ]

accepted : Either CheckError () -> Bool
accepted (Right ()) = True
accepted _ = False

isApplication : Term n -> Bool
isApplication (Apply _ _) = True
isApplication _ = False

isLambda : Term n -> Bool
isLambda (Lambda _ _ _) = True
isLambda _ = False

acceptConstructed : Property
acceptConstructed = property $ do
  sample <- forAll (typedGen 3)
  classify "application at root" (isApplication sample.term)
  classify "lambda at root" (isLambda sample.term)
  assert (accepted (checkErased 100 100 Empty sample.term sample.expected))

stepPreserves : Property
stepPreserves = property $ do
  sample <- forAll (typedGen 3)
  assert (accepted (checkErased 100 100 Empty sample.term sample.expected))
  case step sample.term of
    Nothing => classify "already normal" True
    Just reduced => do
      classify "reducible" True
      assert (accepted (checkErased 100 100 Empty reduced sample.expected))

betaWrapperPreserves : Property
betaWrapperPreserves = property $ do
  sample <- forAll (typedGen 3)
  let wrapped = wrapBeta Linear sample
  assert (accepted (checkErased 100 100 Empty wrapped.term sample.expected))
  case betaCompare 100 wrapped.term sample.term of
    EqualNormalForms => success
    _ => failure

headCompatibility : Property
headCompatibility = property $ do
  sample <- forAll (typedGen 3)
  case weakHead 100 sample.term of
    HeadLimit _ => failure
    HeadForm exposed =>
      case (normalize 100 sample.term, normalize 100 exposed) of
        (Normal original, Normal afterHead) => assert (sameSyntax original afterHead)
        _ => failure

rejectWrongType : Property
rejectWrongType = property $ do
  sample <- forAll (typedGen 3)
  -- Primitive types at Type0 are valid seeds. Choose a known incompatible, well-formed
  -- expectation from the construction recipe, not by filtering with the checker.
  let wrong = if sameSyntax sample.expected (Universe 0) then UnitType else Universe 0
  case checkErased 100 100 Empty sample.term wrong of
    Left (TypeMismatch _ _) => success
    _ => failure

||| Targeted erased-checker properties over a narrow constructive grammar.
||| Samples are neither arbitrary dependent derivations nor runtime-valid terms.
public export
runTypedProperties : IO Bool
runTypedProperties = checkGroup (MkGroup "Fibril erased typing properties"
  [ ("head reduction agrees with full normal forms", headCompatibility)
  , ("constructed erased terms accepted", acceptConstructed)
  , ("one beta step preserves erased checking", stepPreserves)
  , ("typed identity application preserves conversion", betaWrapperPreserves)
  , ("incompatible expected type rejected", rejectWrongType)
  ])
