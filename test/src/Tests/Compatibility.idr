module Tests.Compatibility

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.Compatibility
import Fibril.Core.Erased

%default total

accepted : Either e a -> Bool
accepted (Right _) = True
accepted _ = False

||| Literal compatibility must not weaken equality or invent function coercions.
public export
checks : List (String, Bool)
checks =
  [ ("cumulative upward universe checking",
      accepted (checkErased 40 40 Empty (Universe 0) (Universe 3)))
  , ("cumulative downward universe rejected",
      not (accepted (checkErased 40 40 Empty (Universe 2) (Universe 1))))
  , ("cumulative self-universe rejected",
      not (accepted (checkErased 40 40 Empty (Universe 1) (Universe 1))))
  , ("cumulative comparison is directional",
      case (compatibleTypes 0 (the (Term 0) (Universe 0)) (Universe 1),
            compatibleTypes 0 (the (Term 0) (Universe 1)) (Universe 0)) of
        (Compatible, Incompatible) => True
        _ => False)
  , ("cumulative does not change conversion",
      case betaCompare 0 (the (Term 0) (Universe 0)) (Universe 1) of
        DifferentNormalForms => True
        _ => False)
  , ("cumulative beta normalized levels",
      case compatibleTypes 1
        (the (Term 0) (Apply (Lambda Linear (Universe 2) (Variable FZ)) (Universe 1)))
        (Universe 2) of
        Compatible => True
        _ => False)
  , ("cumulative exhausted comparison stays explicit",
      case compatibleTypes 0
        (the (Term 0) (Apply (Lambda Linear (Universe 2) (Variable FZ)) (Universe 1)))
        (Universe 2) of
        CompatibilityLimit => True
        _ => False)
  , ("cumulative Pi codomain remains invariant",
      case compatibleTypes 0
        (the (Term 0) (Pi Linear (Universe 0) (Universe 0)))
        (Pi Linear (Universe 0) (Universe 1)) of
        Incompatible => True
        _ => False)
  , ("cumulative Pi domain remains invariant",
      case compatibleTypes 0
        (the (Term 0) (Pi Linear (Universe 0) (Universe 0)))
        (Pi Linear (Universe 1) (Universe 0)) of
        Incompatible => True
        _ => False)
  , ("cumulative quantities remain invariant",
      case compatibleTypes 0
        (the (Term 0) (Pi Linear (Universe 0) (Universe 0)))
        (Pi Erased (Universe 0) (Universe 0)) of
        Incompatible => True
        _ => False)
  , ("cumulative expected type still validated",
      not (accepted (checkErased 40 40 Empty (Universe 0)
        (Apply (Universe 0) (Universe 0)))))
  , ("cumulative function argument lifted",
      accepted (inferErased 60 60 Empty
        (Apply (Lambda Erased (Universe 2) (Variable FZ)) (Universe 0))))
  ]
