module Tests.CoreCandidate

import Data.Fin
import Data.List
import Fibril.Core.Erased
import Fibril.Core.Quantity
import Fibril.Core.Runtime
import Fibril.Core.Term
import Fibril.Termination.CoreCandidate

%default total

accepts : Either e a -> Bool
accepts (Right _) = True
accepts _ = False

listTy : Term n
listTy = SeqType "Example.Items" NatType

signature : Term 0
signature = Pi Linear listTy (Pi Linear listTy listTy)

-- Environment in the cons branch: tail, head, accumulator, items, self.
reverseBody : Term 1
reverseBody = Lambda Linear listTy (Lambda Linear listTy
  (SeqCase (Lambda Erased listTy listTy) (Variable (FS FZ)) (Variable FZ)
    (Lambda Linear NatType (Lambda Linear listTy
      (Apply (Apply (Variable (FS (FS (FS (FS FZ))))) (Variable FZ))
             (SeqCons listTy (Variable (FS FZ)) (Variable (FS (FS FZ)))))))))

reverseCandidate : Candidate
reverseCandidate = MkCandidate signature reverseBody

-- The cons branch fails to consume the linear list head.
droppedHead : Term 1
droppedHead = Lambda Linear listTy (Lambda Linear listTy
  (SeqCase (Lambda Erased listTy listTy) (Variable (FS FZ)) (Variable FZ)
    (Lambda Linear NatType (Lambda Linear listTy
      (Apply (Apply (Variable (FS (FS (FS (FS FZ))))) (Variable FZ))
             (Variable (FS (FS FZ))))))))

natSignature : Term 0
natSignature = Pi Linear NatType NatType

-- Well typed and uses its linear input once, but self x loops if unfolded.
loopBody : Term 1
loopBody = Lambda Linear NatType (Apply (Variable (FS FZ)) (Variable FZ))

largeBody : Nat -> Term (S n)
largeBody Z = Variable FZ
largeBody (S n) = NatSucc (largeBody n)

public export
checks : List (String, Bool)
checks =
  [ ("core candidate checks a real scoped reverse accumulator body under hypothetical self",
      accepts (checkHypothesis 512 128 reverseCandidate))
  , ("core candidate independently rejects a dropped linear list head",
      case checkHypothesis 512 128 (MkCandidate signature droppedHead) of
        Left (OrdinaryFailure (BoundUsage Linear Erased)) => True
        _ => False)
  , ("core candidate typing does not claim termination",
      accepts (checkHypothesis 512 128 (MkCandidate natSignature loopBody)))
  , ("core candidate rejects a discarded linear argument",
      case checkHypothesis 512 128 (MkCandidate natSignature (Lambda Linear NatType NatZero)) of
        Left (OrdinaryFailure (BoundUsage Linear Erased)) => True
        _ => False)
  , ("core candidate rejects a mistyped result",
      case checkHypothesis 512 128 (MkCandidate (Pi Unrestricted NatType NatType) (Lambda Unrestricted NatType BoolTrue)) of
        Left (OrdinaryFailure (TypingError (TypeMismatch _ _))) => True
        _ => False)
  , ("core candidate rejects a lambda quantity different from its signature",
      case checkHypothesis 512 128 (MkCandidate natSignature (Lambda Unrestricted NatType (Variable FZ))) of
        Left (OrdinaryFailure (TypingError (TypeMismatch _ _))) => True
        _ => False)
  , ("core candidate rejects list signatures outside the Nat element fragment",
      case checkHypothesis 512 128 (MkCandidate (Pi Linear (SeqType "Example.Items" BoolType) BoolType) (Lambda Linear BoolType (Variable FZ))) of
        Left (Unsupported _) => True
        _ => False)
  , ("core candidate rejects non-functions and non-lambda bodies",
      case (checkHypothesis 512 128 (MkCandidate NatType NatZero),
            checkHypothesis 512 128 (MkCandidate natSignature (Variable FZ))) of
        (Left (Unsupported _), Left (Unsupported _)) => True
        _ => False)
  , ("core candidate rejects unsupported syntax before ordinary checking",
      case checkHypothesis 512 128 (MkCandidate natSignature (Lambda Linear NatType (UnitCase UnitValue (Variable FZ)))) of
        Left (Unsupported _) => True
        _ => False)
  , ("core candidate rejects a dependent function signature",
      case checkHypothesis 512 128 (MkCandidate (Pi Erased (Universe 0) (Variable FZ)) (Lambda Erased (Universe 0) NatZero)) of
        Left (Unsupported _) => True
        _ => False)
  , ("core candidate admits the exact aggregate node boundary",
      accepts (checkHypothesis 512 128 (MkCandidate natSignature (Lambda Linear NatType (largeBody 250)))) &&
      case checkHypothesis 512 128 (MkCandidate natSignature (Lambda Linear NatType (largeBody 251))) of
        Left (AdmissionExhausted _) => True
        _ => False)
  , ("core candidate admits sequence keys before checking signatures and bodies",
      let huge = pack (replicate 4097 'x')
          long = pack (replicate 2048 'x')
          larger = pack (replicate 2049 'y') in
      accepts (checkHypothesis 512 128 (MkCandidate (Pi Erased (SeqType long NatType) NatType) (Lambda Erased (SeqType long NatType) NatZero))) &&
      case (checkHypothesis 512 128 (MkCandidate (Pi Linear (SeqType huge NatType) NatType) loopBody),
            checkHypothesis 512 128 (MkCandidate natSignature (Lambda Linear (SeqType huge NatType) NatZero)),
            checkHypothesis 512 128 (MkCandidate (Pi Linear (SeqType long NatType) NatType) (Lambda Linear (SeqType larger NatType) NatZero))) of
        (Left (AdmissionExhausted _), Left (AdmissionExhausted _), Left (AdmissionExhausted _)) => True
        _ => False)
  , ("core candidate retains ordinary checking exhaustion",
      case checkHypothesis 0 128 (MkCandidate natSignature loopBody) of
        Left (OrdinaryFailure (TypingError CheckingLimit)) => True
        _ => False)
  , ("core candidate retains ordinary reduction exhaustion",
      let domain = Apply (Lambda Erased (Universe 0) (Variable FZ)) NatType
          body = Lambda Linear domain (Variable FZ) in
      case checkHypothesis 512 0 (MkCandidate natSignature body) of
        Left (OrdinaryFailure (TypingError ReductionLimit)) => True
        _ => False)
  ]
