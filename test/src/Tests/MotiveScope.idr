module Tests.MotiveScope

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Elaboration.Expression.Scope
import Fibril.Elaboration.Expression.Motive
import Fibril.Elaboration.Expression.Conversion
import Fibril.Elaboration.Expression.Abstract
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
  [ ("exact subterm abstraction round trips under binders and preserves locals",
      let target : Term 1
          target = Apply (Variable FZ) BoolTrue
          result : Term 1
          result = Pi Erased target (Pi Linear (weaken target) (Apply (weaken (weaken target)) (Variable FZ))) in
        sameSyntax (instantiateTerm target (abstractOver target result)) result)
  , ("guarded conversion recognizes a beta-equivalent type",
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
  , ("NatCase conversion bounds nodes and unsafe redexes in every field",
      let big = largeArgument 510
          redex = Apply (Lambda Erased (Universe 0) (repeated 8)) (largeArgument 80)
          cases : Term 0 -> List (Term 0)
          cases x = [NatCase x NatZero NatZero NatZero, NatCase NatZero x NatZero NatZero,
                     NatCase NatZero NatZero x NatZero, NatCase NatZero NatZero NatZero x] in
        all (not . guardedStepAdmitted) (cases big) &&
        all (not . guardedStepAdmitted) (cases redex) &&
        guardedEqual 8 (the (Term 0) (NatCase NatType (NatSucc NatZero) BoolFalse
          (Lambda Linear NatType BoolTrue))) BoolTrue)
  , ("guarded conversion does not step at zero fuel",
      case guardedNormal 0 (the (Term 0) (Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType)) of Nothing => True; _ => False)
  , ("guarded conversion rejects expansion before substitution",
      let argument = largeArgument 80
          body = repeated 8
          redex = Apply (Lambda Erased (Universe 0) body) argument
       in coreNodes (instantiateTerm argument body) > 512 &&
          case guardedNormal 8 redex of Nothing => True; _ => False)
  , ("guarded conversion admits small string operations and nominal keys",
      guardedEqual 8 (the (Term 0) (StringAppend (StringValue "a") (StringValue "b"))) (StringValue "ab") &&
      guardedEqual 8 (the (Term 0) (StringEqual (StringValue "λ") (StringValue "λ"))) BoolTrue &&
      guardedEqual 8 (the (Term 0) (NominalType "M.T" [Apply (Lambda Erased (Universe 0) (Variable FZ)) StringType] (VariantType [Nothing])))
                     (NominalType "M.T" [StringType] (VariantType [Nothing])) &&
      not (guardedEqual 8 (the (Term 0) (NominalType "M.T" [] (VariantType []))) (NominalType "M.U" [] (VariantType []))))
  , ("guarded conversion bounds character payload and duplication",
      let short = pack (replicate 8192 'a')
          long = pack (replicate 8193 'a')
          duplicate : Term 0
          duplicate = Apply (Lambda Erased StringType (StringAppend (Variable FZ) (Variable FZ))) (StringValue (pack (replicate 3000 'x')))
          nested : Term 0
          nested = Apply (Lambda Erased StringType (Pi Erased UnitType (StringAppend (Variable (FS FZ)) (Variable (FS FZ))))) (StringValue (pack (replicate 3000 'x'))) in
        (case guardedNormal 1 (the (Term 0) (StringValue short)) of Just _ => True; _ => False) &&
        (case guardedNormal 1 (the (Term 0) (StringValue long)) of Nothing => True; _ => False) &&
        guardedStepAdmitted (the (Term 0) (NominalType short [] (VariantType []))) &&
        not (guardedStepAdmitted (the (Term 0) (NominalType long [] (VariantType [])))) &&
        not (guardedStepAdmitted duplicate) && not (guardedStepAdmitted nested) &&
        guardedEqual 0 (the (Term 0) (StringValue long)) (StringValue long) &&
        (case guardedNormal 8 duplicate of Nothing => True; _ => False))
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
