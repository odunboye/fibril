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
import Fibril.Source.Global
import Fibril.Source.Primitive
import Fibril.Driver.Check
import Fibril.Driver.Evaluate
import Fibril.Elaboration.Expression.Parameters
import Fibril.Source.Text
import Fibril.Source.Resolve.Error

%default total

accepted : Bool -> String -> Bool
accepted erased source = case checkSource erased source of
  Right _ => True
  Left _ => False

normalIs : Nat -> String -> String -> Bool
normalIs fuel source expected = case evaluateSource fuel source of
  Right lines => elem ("Normal: " ++ expected) lines
  Left _ => False

natStringMotive : Term n
natStringMotive = Lambda Erased NatType StringType

natStringStep : Term n
natStringStep = Lambda Unrestricted NatType (Lambda Linear StringType (Variable FZ))

-- Regression for the former exact-vector policy: beta reduction exposes 0/1
-- from two omega approximations. Permission joining must accept both stages.
formerEqualityCounterexample : String
formerEqualityCounterexample = "\\(flag : Bool) => \\(x : Unit) => if flag then (\\(ignored : Unit) => ()) x else (\\(y : Unit) => y) x"

public export
checks : List (String, Bool)
checks =
  [ ("Nat formation and structural iterator",
      accepted True "(Nat : Type)" &&
      normalIs 128 "natRec (\\(0 k : Nat) => String) \"a\" (\\(0 k : Nat) => \\(1 x : String) => appendString x \"!\") (Succ (Succ Zero))" "\"a!!\"")
  , ("Nat recursor proposal normalizes a constant motive",
      case implicitArgumentType (At 0 1 1) 16 Empty
        (NatRec (Lambda Erased NatType NatType) NatZero NatZero NatZero) of
        Right (Just NatType) => True
        _ => False)
  , ("runtime predecessor core checks and preserves checking after a step",
      let term = NatRecRuntime natStringMotive (StringValue "base") natStringStep (NatSucc NatZero) in
      case (checkRuntime 512 128 Empty term StringType, step term) of
        (Right _, Just reduced) => case checkRuntime 512 128 Empty reduced StringType of
          Right _ => True
          Left _ => False
        _ => False)
  , ("runtime predecessor core zero and successor computation",
      case (step (the (Term 0) (NatRecRuntime natStringMotive (StringValue "base") natStringStep NatZero)),
            normalize 16 (the (Term 0) (NatRecRuntime natStringMotive (StringValue "base") natStringStep (NatSucc NatZero)))) of
        (Just (StringValue "base"), Normal (StringValue "base")) => True
        _ => False)
  , ("runtime predecessor core permits a linear base exactly once",
      case checkRuntime 512 128 (Extend Empty Linear StringType)
        (NatRecRuntime natStringMotive (Variable FZ) natStringStep NatZero) StringType of
        Right _ => True
        _ => False)
  , ("runtime predecessor core rejects a linear capture in the repeated step",
      let captured = Lambda Unrestricted NatType (Lambda Linear StringType
            (StringAppend (Variable (FS (FS FZ))) (Variable FZ))) in
      case checkRuntime 512 128 (Extend Empty Linear StringType)
        (NatRecRuntime natStringMotive (StringValue "base") captured NatZero) StringType of
        Left (ContextUsage _ Linear Unrestricted) => True
        _ => False)
  , ("runtime predecessor core rejects an erased count",
      case checkRuntime 512 128 (Extend Empty Erased NatType)
        (NatRecRuntime natStringMotive (StringValue "base") natStringStep (Variable FZ)) StringType of
        Left (ContextUsage _ Erased Unrestricted) => True
        _ => False)
  , ("runtime predecessor core requires one induction-result use",
      let discarded = Lambda Unrestricted NatType (Lambda Linear StringType (StringValue "lost")) in
      case checkRuntime 512 128 Empty
        (NatRecRuntime natStringMotive (StringValue "base") discarded NatZero) StringType of
        Left (BoundUsage Linear Erased) => True
        _ => False)
  , ("runtime predecessor recursor computes with an unrestricted count",
      normalIs 128 "natRecWith (\\(0 k : Nat) => Nat) Zero (\\(k : Nat) => \\(1 x : Nat) => natRec (\\(0 j : Nat) => Nat) x (\\(0 j : Nat) => \\(1 y : Nat) => Succ y) k) (Succ (Succ (Succ Zero)))" "(Succ (Succ (Succ Zero)))")
  , ("runtime predecessor recursor rejects a linear count",
      not (accepted False "\\(1 n : Nat) => natRecWith (\\(0 k : Nat) => Nat) Zero (\\(k : Nat) => \\(1 x : Nat) => natRec (\\(0 j : Nat) => Nat) x (\\(0 j : Nat) => \\(1 y : Nat) => Succ y) k) n"))
  , ("Nat recursor rejects linear capture in a repeated step",
      not (accepted False "\\(1 text : String) => natRec (\\(0 k : Nat) => String) \"\" (\\(0 k : Nat) => \\(1 x : String) => appendString x text) Zero"))
  , ("Nat recursor checks a step even at zero",
      not (accepted False "natRec (\\(0 k : Nat) => String) \"ok\" (\\(0 k : Nat) => \\(1 x : String) => True) Zero"))
  , ("Nat predecessor is erased",
      not (accepted False "natRec (\\(0 k : Nat) => Nat) Zero (\\(0 k : Nat) => \\(1 x : Nat) => k) (Succ Zero)"))
  , ("Boolean library functions are not primitives",
      all (\name => case lookupGlobal name primitiveGlobals of Nothing => True; _ => False)
          ["notBool", "andBool", "orBool"])
  , ("Boolean library negation truth table",
      normalIs 128 "notBool True" "False" && normalIs 128 "notBool False" "True")
  , ("Boolean library conjunction truth table",
      normalIs 128 "andBool True True" "True" &&
      normalIs 128 "andBool True False" "False" &&
      normalIs 128 "andBool False True" "False" &&
      normalIs 128 "andBool False False" "False")
  , ("Boolean library disjunction truth table",
      normalIs 128 "orBool True True" "True" &&
      normalIs 128 "orBool True False" "True" &&
      normalIs 128 "orBool False True" "True" &&
      normalIs 128 "orBool False False" "False")
  , ("Boolean library consumes linear parameters exactly once",
      accepted False "\\(1 left : Bool) => \\(1 right : Bool) => andBool left right" &&
      accepted False "\\(1 left : Bool) => \\(1 right : Bool) => orBool left right")
  , ("Boolean library does not discard a linear input on a constant-result path",
      accepted False "\\(1 value : Bool) => andBool False value" &&
      accepted False "\\(1 value : Bool) => orBool True value")
  , ("Boolean library rejects duplication before reduction",
      not (accepted False "(\\(1 value : Bool) => andBool value value) False") &&
      not (accepted False "(\\(1 value : Bool) => orBool value value) True"))
  , ("Boolean library rejects erased extraction",
      not (accepted False "\\(0 value : Bool) => notBool value"))
  , ("Boolean library validates operand types",
      not (accepted False "notBool ()") &&
      not (accepted False "andBool True \"bad\"") &&
      not (accepted True "orBool \"bad\" False"))
  , ("Boolean library supports partial application",
      normalIs 128 "(andBool True) (notBool False)" "True")
  , ("Boolean library can be shadowed",
      normalIs 128 "let (1 notBool : String) = \"local\" in notBool" "\"local\"")
  , ("Bool formation", accepted True "(Bool : Type 0)")
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
