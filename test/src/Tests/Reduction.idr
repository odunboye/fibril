module Tests.Reduction

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Reduction
import Fibril.Core.WeakHead

%default total

identity : Term 0
identity = Lambda Linear (Universe 0) (Variable FZ)

redex : Term 0
redex = Apply identity (Universe 0)

omega : Term 0
omega =
  let self = Lambda Unrestricted (Universe 0) (Apply (Variable FZ) (Variable FZ))
   in Apply self self

isNormal : Term n -> ReductionResult n -> Bool
isNormal expected (Normal actual) = sameSyntax expected actual
isNormal _ _ = False

exhausted : ReductionResult n -> Bool
exhausted (OutOfFuel _) = True
exhausted _ = False

||| Positive, negative, and exhaustion checks for the ordinary reference reducer.
public export
checks : List (String, Bool)
checks =
  [ ("head exact one-step budget",
      case weakHead 1 redex of
        HeadForm term => sameSyntax term (Universe 0)
        _ => False)
  , ("head redex with zero fuel exhausts",
      case weakHead 0 redex of
        HeadLimit _ => True
        _ => False)
  , ("head divergence remains explicit",
      case weakHead 8 omega of
        HeadLimit _ => True
        _ => False)
  , ("head does not inspect lambda body",
      case weakHead 0 (Lambda Linear (Universe 0) (weaken omega)) of
        HeadForm _ => True
        _ => False)
  , ("head does not inspect Pi codomain",
      case weakHead 0 (Pi Linear (Universe 0) (weaken omega)) of
        HeadForm _ => True
        _ => False)
  , ("head leaves neutral argument untouched",
      case weakHead 0 (the (Term 1) (Apply (Variable FZ) (weaken omega))) of
        HeadForm _ => True
        _ => False)
  , ("head follows function spine",
      case weakHead 2
        (Apply (Apply (Lambda Linear (Universe 0) (weaken identity)) (Universe 0)) (Universe 1)) of
        HeadForm term => sameSyntax term (Universe 1)
        _ => False)
  , ("reduction normal at zero fuel", isNormal (Universe 0) (normalize 0 (the (Term 0) (Universe 0))))
  , ("reduction zero fuel rejects redex", exhausted (normalize 0 redex))
  , ("reduction exact one-step budget", isNormal (Universe 0) (normalize 1 redex))
  , ("reduction divergent syntax exhausts", exhausted (normalize 8 omega))
  , ("reduction unused argument not forced",
      isNormal (Universe 1)
        (normalize 1 (Apply (Lambda Erased (Universe 0) (Universe 1))
                            (the (Term 0) omega))))
  , ("reduction under lambda", isNormal identity
      (normalize 1 (Lambda Linear (Universe 0)
        (Apply (Lambda Linear (Universe 0) (Variable FZ)) (Variable FZ)))))
  , ("reduction in Pi domain",
      isNormal (Pi Linear (Universe 0) (Universe 1))
        (normalize 1 (Pi Linear redex (Universe 1))))
  , ("reduction avoids capture",
      isNormal (Lambda Linear (Universe 0) (Variable (FS FZ)))
        (normalize 1 (the (Term 1)
          (Apply (Lambda Linear (Universe 0)
                    (Lambda Linear (Universe 0) (Variable (FS FZ))))
                 (Variable FZ)))))
  , ("conversion beta equality",
      case betaCompare 1 redex (Universe 0) of
        EqualNormalForms => True
        _ => False)
  , ("conversion distinct universes",
      case betaCompare 0 (the (Term 0) (Universe 0)) (Universe 1) of
        DifferentNormalForms => True
        _ => False)
  , ("conversion exhaustion inconclusive",
      case betaCompare 0 redex (Universe 0) of
        Inconclusive => True
        _ => False)
  , ("conversion divergent reflexive input inconclusive",
      case betaCompare 4 omega omega of
        Inconclusive => True
        _ => False)
  ]
