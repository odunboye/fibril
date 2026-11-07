module Tests.Reference.VerifiedReduction

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

