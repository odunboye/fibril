module Tests.Fix

import Data.Fin
import Data.String
import Fibril.Core.FixAdmission
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Evaluation
import Fibril.Core.WeakHead
import Fibril.Core.Pretty
import Fibril.Core.Quantity
import Fibril.Core.Reduction
import Fibril.Core.Runtime
import Fibril.Core.Size
import Fibril.Core.Term
import Fibril.Termination.CoreCalls
import Fibril.Termination.CoreCandidate
import Fibril.Termination.Extract
import Fibril.Termination.SizeChange

%default total

-- Raw Fix terms, admitted only when extraction and the size-change check agree.
natToNat : Term n
natToNat = Pi Linear NatType NatType

-- Environment inside the lambda: parameter 0, self 1.
loopBody : Term 1
loopBody = Lambda Linear NatType (Apply (Variable (FS FZ)) (Variable FZ))

looping : Term 0
looping = Fix natToNat loopBody

terminatingShape : Term 0
terminatingShape = Fix natToNat (Lambda Linear NatType (Variable FZ))

illTypedBody : Term 0
illTypedBody = Fix natToNat (Lambda Linear NatType BoolTrue)

notAFunction : Term 0
notAFunction = Fix NatType NatZero

notAType : Term 0
notAType = Fix NatZero (Lambda Linear NatType (Variable FZ))

isNotAdmitted : Either CheckError a -> Bool
isNotAdmitted (Left (RecursionError _)) = True
isNotAdmitted _ = False

isMismatch : Either CheckError a -> Bool
isMismatch (Left (TypeMismatch _ _)) = True
isMismatch _ = False

isExpectedFunction : Either CheckError a -> Bool
isExpectedFunction (Left (ExpectedFunction _)) = True
isExpectedFunction _ = False

isLeft : Either e a -> Bool
isLeft (Left _) = True
isLeft _ = False

isRejected : Either e a -> Bool
isRejected (Left _) = True
isRejected _ = False


isRight : Either e a -> Bool
isRight (Right _) = True
isRight _ = False

listTy : Term n
listTy = SeqType "Example.Items" NatType

reverseSig : Term 0
reverseSig = Pi Linear listTy (Pi Linear listTy listTy)

-- Environment in the cons branch: tail, head, accumulator, items, self.
withCons : Term 5 -> Term 1
withCons body = Lambda Linear listTy (Lambda Linear listTy
  (SeqCase (Lambda Erased listTy listTy) (Variable (FS FZ)) (Variable FZ)
    (Lambda Linear NatType (Lambda Linear listTy body))))

selfCall : Term 5 -> Term 5 -> Term 5
selfCall first second = Apply (Apply (Variable (FS (FS (FS (FS FZ))))) first) second

reverseBody : Term 1
reverseBody = withCons (selfCall (Variable FZ) (SeqCons listTy (Variable (FS FZ)) (Variable (FS (FS FZ)))))

reverseFix : Term 0
reverseFix = Fix reverseSig reverseBody

-- Rebuilding the scrutinee is not a decrease.
rebuiltFix : Term 0
rebuiltFix = Fix reverseSig (withCons
  (selfCall (SeqCons listTy (Variable (FS FZ)) (Variable FZ)) (Variable (FS (FS FZ)))))

-- Swapping two arguments never decreases either of them.
swapFix : Term 0
swapFix = Fix (Pi Linear NatType (Pi Linear NatType NatType))
  (Lambda Linear NatType (Lambda Linear NatType
    (Apply (Apply (Variable (FS (FS FZ))) (Variable FZ)) (Variable (FS FZ)))))

reverseEdges : List Call
reverseEdges = [Edge 0 0 [[Decreases, Unknown], [Unknown, Unknown]]]

extractsTo : List Call -> Either String (List Call) -> Bool
extractsTo expected (Right actual) = actual == expected
extractsTo _ _ = False

-- Returns the outer variable and ignores an erased parameter: only capture is at issue.
capturing : Term 1
capturing = Fix (Pi Erased NatType NatType) (Lambda Erased NatType (Variable (FS (FS FZ))))

one : Term n
one = NatSucc NatZero

two : Term n
two = NatSucc one

nilList : Term n
nilList = SeqNil listTy

oneTwo : Term 0
oneTwo = SeqCons listTy one (SeqCons listTy two nilList)

twoOne : Term 0
twoOne = SeqCons listTy two (SeqCons listTy one nilList)

reverseCall : Term 0
reverseCall = Apply (Apply reverseFix oneTwo) nilList

headIs : HeadResult n -> Term n -> Bool
headIs (HeadForm t) expected = sameSyntax t expected
headIs _ _ = False

-- Nat recursion through NatCase. Cons-arm environment: predecessor, parameter, self.
natMotive : Term n
natMotive = Lambda Erased NatType NatType

-- countdown n = case n of Zero => 0; Succ p => countdown p
countdownFix : Term 0
countdownFix = Fix natToNat (Lambda Linear NatType
  (NatCase natMotive (Variable FZ) NatZero
    (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (Variable FZ)))))

-- loopNat n = case n of Zero => 0; Succ p => loopNat (Succ p): rebuilt, so not smaller.
rebuiltNatFix : Term 0
rebuiltNatFix = Fix natToNat (Lambda Linear NatType
  (NatCase natMotive (Variable FZ) NatZero
    (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (NatSucc (Variable FZ))))))

-- ack m n = case m of Zero => Succ n
--                     Succ p => case n of Zero => ack p 1
--                                         Succ q => ack p (ack m q)
-- Unrestricted binders because m and n are used more than once. Environments:
-- outer arm: p, n, m, self; inner arm: q, p, n, m, self.
ackSig : Term 0
ackSig = Pi Unrestricted NatType (Pi Unrestricted NatType NatType)

ackFix : Term 0
ackFix = Fix ackSig (Lambda Unrestricted NatType (Lambda Unrestricted NatType
  (NatCase natMotive (Variable (FS FZ)) (NatSucc (Variable FZ))
    (Lambda Unrestricted NatType
      (NatCase natMotive (Variable (FS FZ))
        (Apply (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ)) (NatSucc NatZero))
        (Lambda Unrestricted NatType
          (Apply (Apply (Variable (FS (FS (FS (FS FZ))))) (Variable (FS FZ)))
                 (Apply (Apply (Variable (FS (FS (FS (FS FZ))))) (Variable (FS (FS (FS FZ)))))
                        (Variable FZ)))))))))

-- A recursor used as a helper: double (grow p). Cons-arm environment: predecessor, parameter, self.
doubleStep : Term n
doubleStep = Lambda Erased NatType (Lambda Linear NatType (NatSucc (NatSucc (Variable FZ))))

growFix : Term 0
growFix = Fix natToNat (Lambda Linear NatType
  (NatCase natMotive (Variable FZ) (NatSucc NatZero)
    (Lambda Linear NatType
      (NatRec natMotive NatZero doubleStep (Apply (Variable (FS (FS FZ))) (Variable FZ))))))

-- Recursing THROUGH the recursor: the self call sits inside its step lambda.
throughStep : Term 1
throughStep = Lambda Linear NatType
  (NatRec natMotive NatZero
    (Lambda Erased NatType (Lambda Linear NatType (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ))))
    (Variable FZ))

normalIs : ReductionResult n -> Term n -> Bool
normalIs (Normal t) expected = sameSyntax t expected
normalIs _ _ = False

public export
checks : List (String, Bool)
checks =
  [ ("fix with a well-typed body is not admitted without a termination certificate",
      isNotAdmitted (inferErased 512 128 Empty looping))
  , ("fix of a non-recursive body has no cycles and is admitted",
      isRight (inferErased 512 128 Empty terminatingShape))
  , ("an argument-preserving self call is refused: no argument decreases",
      isNotAdmitted (inferErased 512 128 Empty looping))
  , ("list reversal through fix is admitted because the scrutinee tail decreases",
      isRight (inferErased 512 128 Empty reverseFix))
  , ("list reversal through fix also passes runtime usage checking",
      isRight (inferRuntime 512 128 Empty reverseFix))
  , ("extraction finds the tail decrease and the unknown constructed accumulator",
      extractsTo reverseEdges (extractFix reverseSig reverseBody))
  , ("extraction agrees with the earlier restricted core extractor",
      case Fibril.Termination.CoreCalls.extract 512 128 (MkCandidate reverseSig reverseBody) of
        Right graph => extractsTo graph (extractFix reverseSig reverseBody)
        Left _ => False)
  , ("rebuilding the scrutinee is not a decrease",
      isNotAdmitted (inferErased 512 128 Empty rebuiltFix))
  , ("swapping arguments is refused by the idempotent composite",
      isNotAdmitted (inferErased 512 128 Empty swapFix))
  , ("passing self as an ordinary argument is refused",
      isLeft (extractFix (natToNat {n = 0}) (Lambda Linear NatType (StringAppend (Variable (FS FZ)) (Variable (FS FZ))))))
  , ("an unsaturated recursive call is refused",
      isLeft (extractFix (the (Term 0) (Pi Linear NatType (Pi Linear NatType NatType)))
        (Lambda Linear NatType (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (Variable FZ))))))
  , ("a recursive call under a deferred lambda is refused",
      isLeft (extractFix (natToNat {n = 0})
        (Lambda Linear NatType (PairValue NatType (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (Variable FZ))) NatZero))))
  , ("a let (an immediately applied lambda) runs once, so its calls are extracted",
      extractsTo [Edge 0 0 [[NonIncreasing]]]
        (extractFix (natToNat {n = 0})
          (Lambda Linear NatType (Apply (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (Variable FZ))) (Variable FZ)))))
  , ("a let-bound copy of a variable keeps that variable's size relation",
      extractsTo [Edge 0 0 [[Decreases]]]
        (extractFix (natToNat {n = 0})
          (Lambda Linear NatType
            (NatCase natMotive (Variable FZ) NatZero
              (Lambda Linear NatType
                (Apply (Lambda Linear NatType (Apply (Variable (FS (FS (FS FZ)))) (Variable FZ))) (Variable FZ)))))))
  , ("a let-bound partial application of self is callable and counts its held arguments",
      extractsTo [Edge 0 0 [[Unknown, Unknown], [Unknown, Decreases]]]
        (extractFix (the (Term 0) (Pi Linear NatType (Pi Linear NatType NatType)))
          (Lambda Linear NatType (Lambda Linear NatType
            (Apply (Lambda Linear (Pi Linear NatType NatType)
                     (NatCase natMotive (Variable (FS FZ)) NatZero
                       (Lambda Linear NatType (Apply (Variable (FS FZ)) (Variable FZ)))))
                   (Apply (Variable (FS (FS FZ))) NatZero))))))
  , ("a let-bound alias of self used as a value is refused",
      isLeft (extractFix (the (Term 0) (Pi Linear NatType (Pi Linear NatType NatType)))
        (Lambda Linear NatType (Lambda Linear NatType
          (Apply (Lambda Linear (Pi Linear NatType NatType) (Variable FZ))
                 (Apply (Variable (FS (FS FZ))) NatZero))))))
  , ("a let-bound alias called with too few arguments is refused",
      isLeft (extractFix (the (Term 0) (Pi Linear NatType (Pi Linear NatType (Pi Linear NatType NatType))))
        (Lambda Linear NatType (Lambda Linear NatType (Lambda Linear NatType
          (Apply (Lambda Linear (Pi Linear NatType (Pi Linear NatType NatType))
                   (Apply (Variable FZ) NatZero))
                 (Apply (Variable (FS (FS (FS FZ)))) NatZero)))))))
  , ("unsupported syntax in a recursive body fails closed",
      isLeft (extractFix (natToNat {n = 0})
        (Lambda Linear NatType (IOPure (Variable FZ)))))
  , ("a fix capturing a linear outer variable fails runtime usage checking",
      isRejected (inferRuntime 512 128 (Extend Empty Linear NatType)
        capturing))
  , ("a fix capturing an unrestricted outer variable passes runtime usage checking",
      isRight (inferRuntime 512 128 (Extend Empty Unrestricted NatType)
        capturing))
  , ("fix body is checked against its declared type before admission",
      isMismatch (inferErased 512 128 Empty illTypedBody))
  , ("fix requires a function type",
      isExpectedFunction (inferErased 512 128 Empty notAFunction))
  , ("fix annotation must itself be a type",
      isRejected (inferErased 512 128 Empty notAType))
  , ("runtime checking also refuses an unadmitted fix",
      isRejected (inferRuntime 512 128 Empty looping))
  , ("run-mode evaluation unfolds an admitted fix: reverse [1,2] is [2,1]",
      normalIs (normalizeRun 200 reverseCall) twoOne)
  , ("run-mode evaluation reports fuel exhaustion instead of a partial answer",
      case normalizeRun 2 reverseCall of
        OutOfFuel _ => True
        _ => False)
  , ("run-mode head reduction unfolds fix at the head",
      headIs (weakHeadRun 200 reverseCall) twoOne)
  , ("type-level head reduction still treats fix as neutral",
      case weakHead 200 reverseCall of
        HeadForm t => sameSyntax t reverseCall
        _ => False)
  , ("type-level normalization leaves the recursive call unevaluated",
      normalIs (normalize 200 reverseCall) reverseCall)
  , ("run-mode evaluation never unfolds under a binder, so an open call stays stuck",
      normalIs (normalizeRun 200 (the (Term 0) (Lambda Linear listTy
                  (Apply (Apply (weaken reverseFix) (Variable FZ)) nilList))))
               (the (Term 0) (Lambda Linear listTy
                  (Apply (Apply (weaken reverseFix) (Variable FZ)) nilList))))
  , ("run-mode evaluation agrees with the ordinary reducer on fix-free terms",
      normalIs (normalizeRun 8 (the (Term 0) (Apply (Lambda Linear NatType (Variable FZ)) one))) one)
  , ("nat countdown through NatCase is admitted: the predecessor decreases",
      isRight (inferErased 512 128 Empty countdownFix))
  , ("nat countdown passes runtime usage checking",
      isRight (inferRuntime 512 128 Empty countdownFix))
  , ("rebuilding a nat from its predecessor is not a decrease",
      isNotAdmitted (inferErased 512 128 Empty rebuiltNatFix))
  , ("run-mode evaluation counts a nat down to zero",
      normalIs (normalizeRun 200 (Apply countdownFix (NatSucc (NatSucc (NatSucc NatZero))))) NatZero)
  , ("ackermann is admitted: lexicographic decrease over both arguments",
      isRight (inferErased 512 128 Empty ackFix))
  , ("ackermann evaluates: ack 1 1 is 3",
      normalIs (normalizeRun 2000 (Apply (Apply ackFix one) one)) (NatSucc (NatSucc (NatSucc NatZero))))
  , ("a refusal names the offending call and why",
      case admitFix (natToNat {n = 0}) loopBody of
        Left message => isInfixOf "recursive call 1 of 1" message && isInfixOf "no argument decreases" message
        Right () => False)
  , ("a decreasing recursion is admitted with no message",
      isRight (admitFix reverseSig reverseBody))
  , ("a recursor used as a helper no longer blocks admission",
      isRight (inferErased 512 128 Empty growFix))
  , ("a recursor helper passes runtime usage checking too",
      isRight (inferRuntime 512 128 Empty growFix))
  , ("the recursive call inside a recursor's value position is still extracted",
      case extractFix natToNat (case growFix of
                                  Fix _ body => body
                                  _ => NatZero) of
        Right edges => length edges == 1
        Left _ => False)
  , ("recursing through a recursor step is still refused",
      isLeft (extractFix (natToNat {n = 0}) throughStep))
  , ("run-mode evaluation unfolds a fix feeding a recursor: grow 2 is 4",
      normalIs (normalizeRun 500 (Apply growFix two)) (NatSucc (NatSucc (NatSucc (NatSucc NatZero)))))
  , ("fix is neutral: conversion never unfolds it",
      normalIs (normalize 64 (Apply looping NatZero)) (Apply looping NatZero))
  , ("fix normalization still reduces inside its body",
      normalIs (normalize 64 (the (Term 0) (Fix natToNat (Apply (Lambda Linear NatType (Variable FZ)) (Variable FZ)))))
               (the (Term 0) (Fix natToNat (Variable FZ))))
  , ("fix syntax equality is structural",
      sameSyntax looping looping && not (sameSyntax looping terminatingShape))
  , ("renaming under fix leaves the bound self alone",
      sameSyntax (rename (the (Fin 1 -> Fin 2) FS) (the (Term 1) (Fix natToNat (Variable FZ))))
                 (Fix natToNat (Variable FZ)))
  , ("renaming under fix shifts free variables",
      sameSyntax (rename (the (Fin 1 -> Fin 2) FS) (the (Term 1) (Fix natToNat (Variable (FS FZ)))))
                 (Fix natToNat (Variable (FS (FS FZ)))))
  , ("substitution passes through fix without capturing self",
      sameSyntax (substituteTerm (\_ => NatZero) (the (Term 1) (Fix natToNat (Variable (FS FZ)))))
                 (the (Term 0) (Fix natToNat NatZero)))
  , ("fix counts as one node plus its parts",
      coreNodes looping == 1 + coreNodes (natToNat {n = 0}) + coreNodes loopBody)
  , ("fix renders with its own constructor name",
      isPrefixOf "(Fix " (renderTerm looping))
  ]
