module Tests.Boolean

import Data.Fin
import Data.List
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

accepted : Bool -> String -> Bool
accepted erased source = case checkSource erased source of
  Right _ => True
  Left _ => False

normalIs : Nat -> String -> String -> Bool
normalIs fuel source expected = case evaluateSource fuel source of
  Right lines => elem ("Normal: " ++ expected) lines
  Left _ => False

-- Regression for the former exact-vector policy: beta reduction exposes 0/1
-- from two omega approximations. Permission joining must accept both stages.
formerEqualityCounterexample : String
formerEqualityCounterexample = "\\(flag : Bool) => \\(x : Unit) => if flag then (\\(ignored : Unit) => ()) x else (\\(y : Unit) => y) x"

public export
checks : List (String, Bool)
checks =
  [ ("Bool formation", accepted True "(Bool : Type 0)")
  , ("Bool is not a runtime type value", not (accepted False "Bool"))
  , ("True value", normalIs 0 "True" "True")
  , ("False value", normalIs 0 "False" "False")
  , ("boolean true branch", normalIs 1 "if True then True else False" "True")
  , ("boolean false branch", normalIs 1 "if False then True else False" "False")
  , ("boolean nested syntax",
      normalIs 2 "if if True then False else True then True else False" "False")
  , ("boolean different branch types rejected",
      not (accepted True "if True then True else ()"))
  , ("boolean branch universes not implicitly joined",
      not (accepted True "if True then Type 0 else Type 1"))
  , ("boolean explicit common branch universe",
      accepted True "if True then (Type 0 : Type 2) else (Type 1 : Type 2)")
  , ("boolean condition must have Bool type",
      not (accepted True "if () then True else False"))
  , ("boolean both branches must be typed",
      not (accepted True "if True then () else () ()"))
  , ("boolean both branches must resolve",
      not (accepted True "if True then () else unknown"))
  , ("boolean linear value shared across alternatives",
      accepted False "\\(1 flag : Bool) => \\(1 x : Unit) => if flag then x else x")
  , ("boolean unequal branch use allowed by unrestricted permission",
      accepted False "\\(x : Unit) => if True then x else ()")
  , ("boolean cannot hide unused linear branch",
      not (accepted False "\\(1 x : Unit) => if True then x else ()"))
  , ("boolean erased condition rejected",
      not (accepted False "\\(0 flag : Bool) => if flag then True else False"))
  , ("boolean condition and branch uses add",
      not (accepted False "\\(1 flag : Bool) => if flag then flag else flag"))
  , ("boolean closed unit branches", normalIs 1 "if False then () else ()" "()")
  , ("boolean exact fuel failure",
      case evaluateSource 0 "if True then True else False" of
        Left _ => True
        Right _ => False)
  , ("boolean computational type formation",
      accepted True "if True then Bool else Unit")
  , ("boolean computational type conversion",
      accepted False "(True : if True then Bool else Unit)")
  , ("boolean rejected computational type mismatch",
      not (accepted False "(() : if True then Bool else Unit)"))
  , ("boolean former branch-policy counterexample checks",
      accepted False formerEqualityCounterexample)
  , ("boolean former branch-policy counterexample evaluates and rechecks",
      normalIs 2 formerEqualityCounterexample "(Lam unrestricted Bool (Lam unrestricted Unit (If v1 () v0)))")
  , ("boolean missing else rejected", not (accepted True "if True then True"))
  , ("boolean scrutinee head reduction",
      case weakHead 2 (BoolCase (Apply (Lambda Linear BoolType (Variable FZ)) BoolFalse)
                               BoolTrue (BoolFalse {n = 0})) of
        HeadForm result => sameSyntax result BoolFalse
        _ => False)
  , ("boolean neutral weak head ignores branch computation",
      case stepHead (BoolCase (Variable {n = 1} FZ)
                             (Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue)
                             BoolFalse) of
        Nothing => True
        _ => False)
  , ("boolean neutral full reduction visits branches",
      case step (BoolCase (Variable {n = 1} FZ)
                         (Apply (Lambda Linear BoolType (Variable FZ)) BoolTrue)
                         BoolFalse) of
        Just result => sameSyntax result (BoolCase (Variable FZ) BoolTrue BoolFalse)
        Nothing => False)
  , ("boolean type equality exhaustion stays explicit",
      case inferErased 30 0 Empty
        (BoolCase BoolTrue
          (Lambda Linear (UnitCase UnitValue UnitType) (Variable FZ))
          (Lambda Linear UnitType (Variable FZ))) of
        Left ReductionLimit => True
        _ => False)
  ]
