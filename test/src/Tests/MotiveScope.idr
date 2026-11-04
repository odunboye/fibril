module Tests.MotiveScope

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Motive
import Fibril.Elaboration.Expression.Conversion
import Fibril.Core.Size
import Fibril.Source.Text
import Fibril.Source.Resolve.Error
import Fibril.Core.Context
import Fibril.Core.Runtime

%default total

largeArgument : Nat -> Term 0
largeArgument Z = StringType
largeArgument (S n) = IOType (largeArgument n)

repeated : Nat -> Term 1
repeated Z = Variable FZ
repeated (S n) = Apply (Variable FZ) (repeated n)

public export
checks : List (String, Bool)
checks =
  [ ("guarded conversion recognizes a beta-equivalent type",
      guardedEqual 8 (the (Term 0) (Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType)) StringType)
  , ("guarded conversion sees redexes below a binder",
      guardedEqual 8 (the (Term 0) (Pi Erased StringType (Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType)))
                     (Pi Erased StringType StringType))
  , ("guarded conversion sees redexes inside descriptor lists",
      guardedEqual 8 (the (Term 0) (VariantType [Just (Erased, Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType)]))
                     (VariantType [Just (Erased, StringType)]))
  , ("guarded conversion uses a short-circuit node budget",
      (case guardedNormal 1 (largeArgument 509) of Just _ => True; _ => False) &&
      (case guardedNormal 1 (largeArgument 510) of Nothing => True; _ => False) &&
      (case guardedNormal 1 (largeArgument 512) of Nothing => True; _ => False))
  , ("guarded conversion does not step at zero fuel",
      case guardedNormal 0 (the (Term 0) (Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType)) of Nothing => True; _ => False)
  , ("guarded conversion rejects expansion before substitution",
      let argument = largeArgument 80
          body = repeated 8
          redex = Apply (Lambda Erased (Universe 0) body) argument
       in coreNodes (instantiateTerm argument body) > 512 &&
          case guardedNormal 8 redex of Nothing => True; _ => False)
  , ("guarded conversion excludes string operations and nominal keys",
      (case guardedNormal 8 (the (Term 0) (StringAppend (StringValue "a") (StringValue "b"))) of Nothing => True; _ => False) &&
      (case guardedNormal 8 (the (Term 0) (NominalType "M.T" [] (VariantType [Nothing]))) of Nothing => True; _ => False))
  , ("guarded conversion handles a variant contraction",
      guardedEqual 8 (the (Term 0) (VariantCase BoolType (VariantValue (VariantType [Nothing]) 0 Nothing) [BoolType])) BoolType)
  , ("guarded conversion handles data contraction exposing a beta redex",
      let term : Term 0
          term = BoxCase BoolType (BoxValue BoolType BoolTrue) (Lambda Erased BoolType BoolType)
       in guardedEqual 8 term BoolType && case guardedNormal 1 term of Nothing => True; _ => False)
  , ("motive strengthening rejects the removed pattern variable",
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
