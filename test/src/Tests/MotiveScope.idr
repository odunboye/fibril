module Tests.MotiveScope

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Elaboration.Expression.Scope

%default total

public export
checks : List (String, Bool)
checks =
  [ ("motive strengthening rejects the removed pattern variable",
      case dropNewest (the (Term 1) (Variable FZ)) of Nothing => True; _ => False)
  , ("motive strengthening preserves and shifts an outer variable",
      case dropNewest (the (Term 2) (Variable (FS FZ))) of
        Just result => sameSyntax result (Variable FZ)
        _ => False)
  , ("motive strengthening preserves a result type's own bound variable",
      case dropNewest (the (Term 1) (Pi Erased (Universe 0) (Variable FZ))) of
        Just result => sameSyntax result (Pi Erased (Universe 0) (Variable FZ))
        _ => False)
  , ("motive strengthening rejects dependence in a nested result domain",
      case dropNewest (the (Term 1) (Pi Linear (Variable FZ) BoolType)) of Nothing => True; _ => False)
  , ("motive strengthening rejects dependence under a nested binder",
      case dropNewest (the (Term 1) (Pi Linear BoolType (Variable (FS FZ)))) of Nothing => True; _ => False)
  , ("motive size counts unary and binary result type nodes",
      typeNodes (the (Term 0) (BoxType Erased (Sigma Linear Linear BoolType BoolType))) == 4)
  ]
