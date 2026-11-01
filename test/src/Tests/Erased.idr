module Tests.Erased

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Erased

%default total

succeeds : Either e a -> Bool
succeeds (Right _) = True
succeeds _ = False

hasType : Term n -> Either CheckError (Term n) -> Bool
hasType expected (Right actual) = sameSyntax expected actual
hasType _ _ = False

-- A : Type 0, x : A.
context : Context 2
context = Extend (Extend Empty Erased (Universe 0)) Linear (Variable FZ)

-- (A : Type 0) -> (x : A) -> A.
identity : Term 0
identity = Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))

identityType : Term 0
identityType = Pi Erased (Universe 0) (Pi Linear (Variable FZ) (Variable (FS FZ)))

||| Tests for the erased ordinary checker; not evidence of runtime linear safety.
public export
checks : List (String, Bool)
checks =
  [ ("erased universe hierarchy",
      hasType (Universe 1) (inferErased 20 20 Empty (Universe 0)))
  , ("erased dependent variable lookup",
      hasType (Variable (FS FZ)) (inferErased 20 20 context (Variable FZ)))
  , ("erased polymorphic identity",
      succeeds (checkErased 30 30 Empty identity identityType))
  , ("erased dependent application",
      hasType (Variable (FS FZ))
        (inferErased 30 30 context
          (Apply (Lambda Linear (Variable (FS FZ)) (Variable FZ)) (Variable FZ))))
  , ("erased rejects Type in itself",
      case checkErased 20 20 Empty (Universe 0) (Universe 0) of
        Left TypeMismatch => True
        _ => False)
  , ("erased rejects nonfunction application",
      case inferErased 20 20 Empty (Apply (Universe 0) (Universe 0)) of
        Left ExpectedFunction => True
        _ => False)
  , ("erased rejects wrong argument",
      case inferErased 30 30 Empty
        (Apply (Lambda Linear (Universe 0) (Variable FZ)) (Universe 0)) of
        Left TypeMismatch => True
        _ => False)
  , ("erased rejects illformed context",
      case checkErasedContext 20 20
        (Extend context Erased (Variable FZ)) of
        Left ExpectedUniverse => True
        _ => False)
  , ("erased validates expected type",
      case checkErased 20 20 context (Variable FZ) (Variable FZ) of
        Left ExpectedUniverse => True
        _ => False)
  , ("erased checking budget explicit",
      case inferErased 0 20 Empty (Universe 0) of
        Left CheckingLimit => True
        _ => False)
  , ("erased beta conversion in annotation",
      succeeds (checkErased 40 40 Empty
        (Lambda Linear (Apply (Lambda Linear (Universe 1) (Variable FZ)) (Universe 0))
          (Variable FZ))
        (Pi Linear (Universe 0) (Universe 0))))
  , ("erased reduction limit is not mismatch",
      case checkErased 40 0 Empty
        (Lambda Linear (Apply (Lambda Linear (Universe 1) (Variable FZ)) (Universe 0))
          (Variable FZ))
        (Pi Linear (Universe 0) (Universe 0)) of
        Left ReductionLimit => True
        _ => False)
  , ("erased quantity mismatch rejected",
      case checkErased 30 30 Empty
        (Lambda Linear (Universe 0) (Variable FZ))
        (Pi Erased (Universe 0) (Universe 0)) of
        Left TypeMismatch => True
        _ => False)
  , ("erased can discard linear variable in type-only judgment",
      succeeds (inferErased 20 20 context (Universe 0)))
  ]
