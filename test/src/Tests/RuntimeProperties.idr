module Tests.RuntimeProperties

import Data.Fin
import Data.Vect
import Hedgehog
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Context
import Fibril.Core.Usage
import Fibril.Core.Reduction
import Fibril.Core.Runtime

%default total

-- A : Type0 (erased), x : A (linear). Every generated term captures x once.
context : Context 2
context = Extend (Extend Empty Erased (Universe 0)) Linear (Variable FZ)

record Sample where
  constructor MkSample
  term : Term 2
  expected : Term 2

Show Sample where
  show (MkSample term ty) = renderTerm term ++ " : " ++ renderTerm ty

base : Sample
base = MkSample (Variable FZ) (Variable (FS FZ))

capture : Sample -> Sample
capture (MkSample term ty) =
  MkSample (Lambda Erased (Universe 0) (weaken term))
           (Pi Erased (Universe 0) (weaken ty))

identityApplication : Quantity -> Sample -> Sample
identityApplication q (MkSample term ty) =
  MkSample (Apply (Lambda q ty (Variable FZ)) term) ty

-- Construct complete term/type pairs together; no checker-driven filtering.
runtimeGen : Nat -> Gen Sample
runtimeGen Z = pure base
runtimeGen (S depth) =
  choice
    [ pure base
    , capture <$> runtimeGen depth
    , identityApplication Linear <$> runtimeGen depth
    , (\sample => MkSample (UnitCase UnitValue sample.term) sample.expected) <$> runtimeGen depth
    , (\sample => MkSample (BoolCase BoolFalse sample.term (identityApplication Linear sample).term)
                           sample.expected) <$> runtimeGen depth
    ]

hasLinearCapture : Either RuntimeError (RuntimeResult 2) -> Bool
hasLinearCapture (Right result) = result.usage == [Linear, Erased]
hasLinearCapture _ = False

acceptConstructed : Property
acceptConstructed = property $ do
  sample <- forAll (runtimeGen 4)
  assert (hasLinearCapture (checkRuntime 100 100 context sample.term sample.expected))

preserveStep : Property
preserveStep = property $ do
  sample <- forAll (runtimeGen 4)
  assert (hasLinearCapture (checkRuntime 100 100 context sample.term sample.expected))
  case step sample.term of
    Nothing => classify "already normal" True
    Just reduced => do
      classify "reducible" True
      assert (hasLinearCapture (checkRuntime 100 100 context reduced sample.expected))

preserveNormal : Property
preserveNormal = property $ do
  sample <- forAll (runtimeGen 4)
  case normalize 100 sample.term of
    Normal reduced =>
      assert (hasLinearCapture (checkRuntime 100 100 context reduced sample.expected))
    OutOfFuel _ => failure

rejectDuplication : Property
rejectDuplication = property $ do
  sample <- forAll (runtimeGen 4)
  let duplicated = identityApplication Unrestricted sample
  case checkRuntime 100 100 context duplicated.term duplicated.expected of
    Left (ContextUsage 0 Linear Unrestricted) => success
    _ => failure

rejectErasedExtraction : Property
rejectErasedExtraction = property $ do
  sample <- forAll (runtimeGen 4)
  let erasedContext = Extend (Extend Empty Erased (Universe 0)) Erased (Variable FZ)
  case checkRuntime 100 100 erasedContext sample.term sample.expected of
    Left (ContextUsage 0 Erased Linear) => success
    _ => failure

-- Closed Unit programs constructed without checker filtering.
unitGen : Nat -> Gen (Term 0)
unitGen Z = pure UnitValue
unitGen (S depth) =
  choice
    [ pure UnitValue
    , UnitCase UnitValue <$> unitGen depth
    , BoolCase <$> element [BoolTrue, BoolFalse] <*> unitGen depth <*> unitGen depth
    , Apply (Lambda Linear UnitType (Variable FZ)) <$> unitGen depth
    , (\body => Apply (Lambda Erased UnitType (weaken body)) UnitValue) <$> unitGen depth
    ]

unitPrograms : Property
unitPrograms = property $ do
  term <- forAll (unitGen 6)
  case checkRuntime 100 100 Empty term UnitType of
    Left _ => failure
    Right checked => assert (checked.usage == [])
  case normalize 100 term of
    OutOfFuel _ => failure
    Normal result => do
      assert (sameSyntax result UnitValue)
      case checkRuntime 100 100 Empty result UnitType of
        Left _ => failure
        Right checked => assert (checked.usage == [])

-- Both ambient variables are unrestricted; branches may observe 0, 1, or omega.
permissionContext : Context 2
permissionContext = Extend (Extend Empty Unrestricted BoolType) Unrestricted UnitType

permissionGen : Nat -> Gen (Term 2)
permissionGen Z = element [UnitValue, Variable FZ]
permissionGen (S depth) =
  choice
    [ element [UnitValue, Variable FZ]
    , Apply (Lambda Linear UnitType (Variable FZ)) <$> permissionGen depth
    , (\body => Apply (Lambda Unrestricted UnitType (weaken body)) (Variable FZ)) <$>
        permissionGen depth
    , UnitCase (Variable FZ) <$> permissionGen depth
    , BoolCase <$> element [BoolTrue, BoolFalse, Variable (FS FZ)] <*>
        permissionGen depth <*> permissionGen depth
    ]

underPermissions : Term 2 -> Bool
underPermissions term =
  case checkRuntime 100 100 permissionContext term UnitType of
    Right _ => True
    Left _ => False

preserveBranchPermissions : Property
preserveBranchPermissions = property $ do
  term <- forAll (permissionGen 4)
  assert (underPermissions term)
  case step term of
    Nothing => success
    Just reduced => assert (underPermissions reduced)
  case normalize 100 term of
    OutOfFuel _ => failure
    Normal reduced => assert (underPermissions reduced)

||| Sample ordinary resource properties over narrow open-context grammars.
||| These are not proofs of quantitative subject reduction or erasure correctness.
public export
runRuntimeProperties : IO Bool
runRuntimeProperties = checkGroup (MkGroup "Fibril runtime usage properties"
  [ ("branch permissions survive sampled reduction", preserveBranchPermissions)
  , ("closed Unit programs check and normalize to unit", unitPrograms)
  , ("constructed terms capture linear input once", acceptConstructed)
  , ("one beta step preserves linear capture", preserveStep)
  , ("normalization preserves linear capture", preserveNormal)
  , ("unrestricted argument rejects linear capture", rejectDuplication)
  , ("erased input cannot be extracted", rejectErasedExtraction)
  ])
