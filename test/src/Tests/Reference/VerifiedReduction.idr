module Tests.Reference.VerifiedReduction

import Fibril.Foundation.DeMorgan.Interval
import Fibril.Foundation.DeMorgan.NormalForm
import Fibril.Foundation.DeMorgan.Sorted

import Fibril.Foundation.DeMorgan.VerifiedReduction

%default total

-- Positive and negative occurrences deliberately have the same truth value.
independent : SignedAssignment
independent _ _ = True

emptyProof : evalDNF Tests.Reference.VerifiedReduction.independent (verifiedReduce []) = evalDNF Tests.Reference.VerifiedReduction.independent []
emptyProof = evalVerifiedReduce independent []

duplicateProof : evalDNF Tests.Reference.VerifiedReduction.independent (verifiedReduce [[(0, False), (0, False)], [(0, False)]]) =
                 evalDNF Tests.Reference.VerifiedReduction.independent [[(0, False), (0, False)], [(0, False)]]
duplicateProof = evalVerifiedReduce independent [[(0, False), (0, False)], [(0, False)]]

nonBooleanProof : evalDNF Tests.Reference.VerifiedReduction.independent (verifiedReduce [[(0, False), (0, True)]]) = True
nonBooleanProof = trans (evalVerifiedReduce independent [[(0, False), (0, True)]]) Refl

-- No ordering laws are required for observation preservation.
strange : Nat -> Nat -> Ordering
strange _ _ = GT

strangeProof : observes (\x => x == 2) (insertionSortBy Tests.Reference.VerifiedReduction.strange [1, 2, 1]) =
               observes (\x => x == 2) [1, 2, 1]
strangeProof = observesInsertionSortBy strange (\x => x == 2) [1, 2, 1]


-- Raw syntax exercises both De Morgan branches and independent signs.
rawPositive : evalDNF Tests.Reference.VerifiedReduction.independent
  (verifiedNormal False (Meet (Var 0) (Reverse (Var 0)))) = True
rawPositive = trans (evalVerifiedNormal independent False (Meet (Var 0) (Reverse (Var 0)))) Refl

rawNegative : evalDNF Tests.Reference.VerifiedReduction.independent
  (verifiedNormal True (Join (Var 0) (Reverse (Var 0)))) = True
rawNegative = trans (evalVerifiedNormal independent True (Join (Var 0) (Reverse (Var 0)))) Refl

rawNested : (env : SignedAssignment) -> (polarity : Bool) ->
  evalDNF env (verifiedNormal polarity (Reverse (Join Zero (Meet (Var 1) One)))) =
  evalSigned env polarity (Reverse (Join Zero (Meet (Var 1) One)))
rawNested env polarity = evalVerifiedNormal env polarity (Reverse (Join Zero (Meet (Var 1) One)))
