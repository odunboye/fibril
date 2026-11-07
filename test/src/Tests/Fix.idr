module Tests.Fix

import Data.Fin
import Data.String
import Fibril.Core.Context
import Fibril.Core.Erased
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
  , ("passing self as an argument is refused",
      isLeft (extractFix (natToNat {n = 0}) (Lambda Linear NatType (Apply (Lambda Linear natToNat NatZero) (Variable (FS FZ))))))
  , ("an unsaturated recursive call is refused",
      isLeft (extractFix (the (Term 0) (Pi Linear NatType (Pi Linear NatType NatType)))
        (Lambda Linear NatType (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (Variable FZ))))))
  , ("a recursive call under a non-leading lambda is refused",
      isLeft (extractFix (natToNat {n = 0})
        (Lambda Linear NatType (Apply (Lambda Linear NatType (Apply (Variable (FS (FS FZ))) (Variable FZ))) (Variable FZ)))))
  , ("unsupported syntax in a recursive body fails closed",
      isLeft (extractFix (natToNat {n = 0})
        (Lambda Linear NatType (NatRec (Lambda Erased NatType NatType) NatZero (Lambda Erased NatType (Lambda Linear NatType (Variable FZ))) (Variable FZ)))))
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
