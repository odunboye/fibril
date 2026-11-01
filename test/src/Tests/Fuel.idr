module Tests.Fuel

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.Reduction.Fuel

%default total

pending : Term 0
pending = UnitCase UnitValue (BoolCase BoolFalse BoolFalse BoolTrue)

sample : Term 0
sample = Apply (Lambda Linear BoolType (Variable FZ)) pending

finished : normalize 3 Tests.Fuel.sample = Normal BoolTrue
finished = Refl

unfinished : normalize 1 Tests.Fuel.sample = OutOfFuel Tests.Fuel.pending
unfinished = Refl

splitEvidence :
  normalize (1 + 2) Tests.Fuel.sample =
    continueNormalization 2 (normalize 1 Tests.Fuel.sample)
splitEvidence = normalizeSplit 1 2 sample

moreEvidence : normalize (3 + 17) Tests.Fuel.sample = Normal BoolTrue
moreEvidence = normalizeMore 3 17 sample BoolTrue finished

resumeEvidence : normalize (1 + 2) Tests.Fuel.sample = normalize 2 Tests.Fuel.pending
resumeEvidence = normalizeResume 1 2 sample pending unfinished

normalEvidence : step (BoolTrue {n = 0}) = Nothing
normalEvidence = normalHasNoStep 3 sample BoolTrue finished

-- Closed but ill typed: self application is rejected by the checker.
-- A proof of bounded fuel behavior does not assert this syntax normalizes.
self : Term 0
self = Lambda Unrestricted UnitType (Apply (Variable FZ) (Variable FZ))

omega : Term 0
omega = Apply self self

loopEvidence :
  normalize (2 + 3) Tests.Fuel.omega =
    continueNormalization 3 (normalize 2 Tests.Fuel.omega)
loopEvidence = normalizeSplit 2 3 omega

sameResult : ReductionResult n -> ReductionResult n -> Bool
sameResult (Normal left) (Normal right) = sameSyntax left right
sameResult (OutOfFuel left) (OutOfFuel right) = sameSyntax left right
sameResult _ _ = False

public export
checks : List (String, Bool)
checks =
  [ ("fuel splitting theorem witness across beta and data steps",
      case splitEvidence of
        Refl => sameResult (normalize 3 sample) (continueNormalization 2 (normalize 1 sample)))
  , ("fuel success remains stable",
      case moreEvidence of
        Refl => sameResult (normalize 20 sample) (Normal BoolTrue))
  , ("fuel exhausted remainder resumes exactly",
      case resumeEvidence of
        Refl => sameResult (normalize 3 sample) (normalize 2 pending))
  , ("fuel actual successful result has no next step",
      case normalEvidence of
        Refl => case step (BoolTrue {n = 0}) of
          Nothing => True
          Just _ => False)
  , ("fuel zero recognizes normal syntax",
      sameResult (continueNormalization 0 (normalize 0 (BoolTrue {n = 0}))) (Normal BoolTrue))
  , ("fuel zero continuation retains unfinished syntax",
      sameResult (continueNormalization 0 (normalize 1 sample)) (OutOfFuel pending))
  , ("fuel splitting does not assume termination",
      case loopEvidence of
        Refl => sameResult (normalize 5 omega) (OutOfFuel omega))
  , ("fuel result data is not a normality certificate",
      case continueNormalization 10 (Normal sample) of
        Normal result => case step result of
          Just _ => True
          Nothing => False
        OutOfFuel _ => False)
  ]
