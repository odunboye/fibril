module Tests.CoreCandidate

import Data.Fin
import Data.List
import Fibril.Core.Erased
import Fibril.Core.Quantity
import Fibril.Core.Runtime
import Fibril.Core.Term
import Fibril.Termination.CoreCandidate
import Fibril.Termination.SizeChange
import Fibril.Termination.CoreCalls
import Fibril.Termination.CoreCheck

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

withCons : Term 5 -> Term 1
withCons body = Lambda Linear listTy (Lambda Linear listTy
  (SeqCase (Lambda Erased listTy listTy) (Variable (FS FZ)) (Variable FZ)
    (Lambda Linear NatType (Lambda Linear listTy body))))

selfCall : Term 5 -> Term 5 -> Term 5
selfCall first second = Apply (Apply (Variable (FS (FS (FS (FS FZ))))) first) second

-- Reconstructing the scrutinee is not a decrease.
reconstructed : Candidate
reconstructed = MkCandidate signature (withCons
  (selfCall (SeqCons listTy (Variable (FS FZ)) (Variable FZ)) (Variable (FS (FS FZ)))))

-- The recursive call nested in an argument must not be overlooked.
nestedCall : Candidate
nestedCall = MkCandidate signature (withCons
  (selfCall (selfCall (Variable FZ) (Variable (FS (FS FZ))))
            (SeqCons listTy (Variable (FS FZ)) (SeqNil listTy))))

-- A let-like application passes self as a value instead of a direct target.
indirectCall : Candidate
indirectCall = MkCandidate signature (withCons
  (Apply
    (Lambda Unrestricted (Pi Linear listTy (Pi Linear listTy listTy))
      (Apply (Apply (Variable FZ) (Variable (FS FZ)))
             (SeqCons listTy (Variable (FS (FS FZ))) (Variable (FS (FS (FS FZ)))))))
    (Variable (FS (FS (FS (FS FZ)))))))

secondScrutinee : Candidate
secondScrutinee = MkCandidate signature
  (Lambda Linear listTy (Lambda Linear listTy
    (SeqCase (Lambda Erased listTy listTy) (Variable FZ) (Variable (FS FZ))
      (Lambda Linear NatType (Lambda Linear listTy
        (selfCall (SeqCons listTy (Variable (FS FZ)) (Variable (FS (FS (FS FZ))))) (Variable FZ)))))))

nilCall : Candidate
nilCall = MkCandidate signature (Lambda Linear listTy (Lambda Linear listTy
  (SeqCase (Lambda Erased listTy listTy) (Variable (FS FZ))
    (Apply (Apply (Variable (FS (FS FZ))) (SeqNil listTy)) (Variable FZ))
    (Lambda Linear NatType (Lambda Linear listTy
      (selfCall (Variable FZ) (SeqCons listTy (Variable (FS FZ)) (Variable (FS (FS FZ))))))))))

duplicateCalls : Candidate
duplicateCalls = MkCandidate signature (Lambda Linear listTy (Lambda Linear listTy
  (SeqCase (Lambda Erased listTy listTy) (Variable (FS FZ))
    (Apply (Apply (Variable (FS (FS FZ))) (SeqNil listTy)) (Variable FZ))
    (Lambda Linear NatType (Lambda Linear listTy
      (selfCall (SeqCons listTy (Variable (FS FZ)) (Variable FZ)) (Variable (FS (FS FZ)))))))))

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
  , ("core call extraction tracks tail and constructed accumulator",
      case Fibril.Termination.CoreCalls.extract 512 128 reverseCandidate of
        Right graph => graph == [Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]]] &&
                       accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate graph)
        _ => False)
  , ("core call extraction follows the matched parameter rather than its position",
      case Fibril.Termination.CoreCalls.extract 512 128 secondScrutinee of
        Right graph => graph == [Edge 0 0 [[Unknown, Unknown], [Unknown, Decreases]]]
        _ => False)
  , ("core call extraction retains both branches in order, without nil descent",
      case Fibril.Termination.CoreCalls.extract 512 128 nilCall of
        Right graph => graph == [Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]],
                                 Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]]]
        _ => False)
  , ("core graph checker rejects forged, missing, extra and stale calls",
      let edge = Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]]
          forged = Edge 0 0 [[Decreases, Unknown], [Unknown, Decreases]] in
      accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [edge]) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [forged])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [edge, edge])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 reconstructed [edge])) &&
      case Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [edge, edge, edge] of
        Left ProposedCallsExhausted => True
        _ => False)
  , ("core certificate check binds a closure to the same actual body and calls",
      let decreasing = Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]]
          reconstructedEdge = Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]] in
      case Fibril.Termination.CoreCheck.verifyCore 512 128 reverseCandidate [decreasing] [decreasing] of
        Right GraphAccepted =>
          not (accepts (Fibril.Termination.CoreCheck.verifyCore 512 128 reconstructed [decreasing] [decreasing])) &&
          case Fibril.Termination.CoreCheck.verifyCore 512 128 reconstructed [reconstructedEdge] [reconstructedEdge] of
            Right (GraphRejected _) => case Fibril.Termination.CoreCheck.verifyCore 512 128 reverseCandidate [decreasing] [] of
              Right (GraphRejected _) => True
              _ => False
            _ => False
        _ => False)
  , ("core certificate admission exhaustion is inconclusive",
      let edge = Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]] in
      case Fibril.Termination.CoreCheck.verifyCore 512 128 reverseCandidate [edge] (replicate 33 edge) of
        Right (GraphInconclusive _) => True
        _ => False)
  , ("core graph checker validates branch ordering and matrix shape",
      let nil = Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]]
          cons = Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]]
          malformed = Edge 0 0 [[Decreases], [Unknown, Unknown]] in
      accepts (Fibril.Termination.CoreCheck.check 512 128 nilCall [nil, cons]) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 nilCall [cons, nil])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 nilCall [nil])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [malformed])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 reverseCandidate [Edge 0 1 [[Decreases, Unknown], [Unknown, Unknown]]])))
  , ("core graph checker preserves duplicate call-site multiplicity",
      let edge = Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]] in
      case Fibril.Termination.CoreCalls.extract 512 128 duplicateCalls of
        Right calls => calls == [edge, edge] &&
                       accepts (Fibril.Termination.CoreCheck.check 512 128 duplicateCalls calls) &&
                       not (accepts (Fibril.Termination.CoreCheck.check 512 128 duplicateCalls [edge]))
        _ => False)
  , ("core graph checker handles second scrutinee and rejects unsupported nested calls",
      let edge = Edge 0 0 [[Unknown, Unknown], [Unknown, Decreases]] in
      accepts (Fibril.Termination.CoreCheck.check 512 128 secondScrutinee [edge]) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 nestedCall [])) &&
      not (accepts (Fibril.Termination.CoreCheck.check 512 128 indirectCall [])))
  , ("core call extraction does not claim a reconstructed list decreases",
      case Fibril.Termination.CoreCalls.extract 512 128 reconstructed of
        Right graph => graph == [Edge 0 0 [[Unknown, Unknown], [Unknown, NonIncreasing]]]
        _ => False)
  , ("core call extraction rejects a nested call even when ordinary typing succeeds",
      accepts (checkHypothesis 512 128 nestedCall) &&
      case Fibril.Termination.CoreCalls.extract 512 128 nestedCall of
        Left (UnsupportedCore _) => True
        _ => False)
  , ("core call extraction rejects self passed indirectly as a value",
      accepts (checkHypothesis 512 128 indirectCall) &&
      case Fibril.Termination.CoreCalls.extract 512 128 indirectCall of
        Left (UnsupportedCore _) => True
        _ => False)
  , ("core call extraction retains ordinary typing failures",
      case Fibril.Termination.CoreCalls.extract 512 128 (MkCandidate signature droppedHead) of
        Left (HypothesisFailure _) => True
        _ => False)
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
