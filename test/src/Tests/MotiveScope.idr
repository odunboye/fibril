module Tests.MotiveScope

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Motive
import Fibril.Source.Text
import Fibril.Source.Resolve.Error
import Fibril.Core.Context
import Fibril.Core.Runtime

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
  , ("substitution size preserves local binders and counts replaced outer variables",
      let weights : Fin 1 -> Nat
          weights _ = 4
       in substitutionNodes weights (Pi Erased (Universe 0) (Variable (FS FZ))) == 6)
  , ("canonical dependent unary motive is independently runtime checked",
      case unaryMotive (At 0 1 1) Erased (the (Term 0) (Universe 0))
             (Pi Linear (Variable FZ) (Variable (FS FZ))) of
        Right motive =>
          let branch = Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))
              term = BoxCase motive (BoxValue (BoxType Erased (Universe 0)) StringType) branch
           in case checkRuntime 256 128 Empty term (Pi Linear StringType StringType) of
                Right _ => True
                _ => False
        _ => False)
  , ("motive size counts unary and binary result type nodes",
      typeNodes (the (Term 0) (BoxType Erased (Sigma Linear Linear BoolType BoolType))) == 4)
  ]
