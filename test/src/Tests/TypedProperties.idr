module Tests.TypedProperties

import Data.Fin
import Data.Vect
import Hedgehog
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Context
import Fibril.Core.Reduction
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
  [ Sample (Universe 0) (Universe 1)
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
    , wrapLambda <$> element [Erased, Linear, Unrestricted] <*> typedGen depth
    , wrapBeta <$> element [Erased, Linear, Unrestricted] <*> typedGen depth
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

rejectWrongUniverse : Property
rejectWrongUniverse = property $ do
  sample <- forAll (typedGen 3)
  -- Seeds and wrappers have types which cannot beta-reduce to Type 8.
  -- Type 8 is itself valid, so rejection must be an actual type mismatch.
  case checkErased 100 100 Empty sample.term (Universe 8) of
    Left TypeMismatch => success
    _ => failure

||| Targeted erased-checker properties over a narrow constructive grammar.
||| Samples are neither arbitrary dependent derivations nor runtime-valid terms.
public export
runTypedProperties : IO Bool
runTypedProperties = checkGroup (MkGroup "Fibril erased typing properties"
  [ ("constructed erased terms accepted", acceptConstructed)
  , ("one beta step preserves erased checking", stepPreserves)
  , ("typed identity application preserves conversion", betaWrapperPreserves)
  , ("wrong universe expectation rejected", rejectWrongUniverse)
  ])
