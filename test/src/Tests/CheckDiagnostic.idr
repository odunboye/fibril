module Tests.CheckDiagnostic

import Data.List
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Pretty
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Driver.Check
import Fibril.Driver.Evaluate

%default total

public export
checks : List (String, Bool)
checks =
  [ ("type diagnostic carries both closed types",
      case checkErased 30 30 Empty BoolTrue UnitType of
        Left (TypeMismatch actual expected) =>
          sameSyntax actual BoolType && sameSyntax expected UnitType
        _ => False)
  , ("type diagnostic retains open scope",
      let context = Extend (Extend Empty Erased (Universe 0)) Linear (Variable FZ)
       in case checkErased 30 30 context (Variable FZ) BoolType of
         Left (TypeMismatch actual expected) =>
           renderTerm actual == "v1" && renderTerm expected == "Bool"
         _ => False)
  , ("shape diagnostic shows exposed nonfunction type",
      case inferErased 30 30 Empty (Apply UnitValue UnitValue) of
        Left (ExpectedFunction found) => sameSyntax found UnitType
        _ => False)
  , ("shape diagnostic shows nonuniverse type",
      case inferErased 30 30 Empty (Lambda Linear UnitValue (Variable FZ)) of
        Left (ExpectedUniverse found) => sameSyntax found UnitType
        _ => False)
  , ("branch diagnostic carries both inferred types",
      case inferErased 30 30 Empty (BoolCase BoolTrue BoolTrue UnitValue) of
        Left (BranchTypeMismatch yesType noType) =>
          sameSyntax yesType BoolType && sameSyntax noType UnitType
        _ => False)
  , ("mismatch rendering includes actual and expected",
      show (TypeMismatch (BoolType {n = 0}) UnitType) ==
        "Inferred type is not compatible with expected type; inferred: Bool; expected: Unit")
  , ("shape rendering includes found type",
      show (ExpectedFunction (UnitType {n = 0})) ==
        "Expected a dependent function type; found: Unit")
  , ("diagnostic rendering does not normalize payload",
      show (TypeMismatch (UnitCase UnitValue (BoolType {n = 0})) UnitType) ==
        "Inferred type is not compatible with expected type; inferred: (CaseUnit () Bool); expected: Unit")
  , ("runtime structured driver retains type payload",
      case checkSourceDetailed False "(True : Unit)" of
        Left (RuntimeFailure (TypingError (TypeMismatch actual expected))) =>
          sameSyntax actual BoolType && sameSyntax expected UnitType
        _ => False)
  , ("erased structured driver retains type payload",
      case checkSourceDetailed True "(Type 0 : Type 0)" of
        Left (ErasedFailure (TypeMismatch actual expected)) =>
          sameSyntax actual (Universe 1) && sameSyntax expected (Universe 0)
        _ => False)
  , ("evaluation structured driver retains branch payload",
      case evaluateSourceDetailed 10 "if True then True else ()" of
        Left (RuntimeFailure (TypingError (BranchTypeMismatch yesType noType))) =>
          sameSyntax yesType BoolType && sameSyntax noType UnitType
        _ => False)
  , ("evaluation limit remains structured and separate",
      case evaluateSourceDetailed 0 "if True then True else False" of
        Left EvaluationLimit => True
        _ => False)
  , ("post-reduction structured rendering retains runtime error",
      show (PostReductionFailure (BoundUsage Linear Erased)) ==
        "Post-reduction checking failed: Binder usage: expected 1, observed 0")
  , ("mismatch driver adds no fabricated location",
      renderDriverError "test.fib" "(True : Unit)"
        (RuntimeFailure (TypingError (TypeMismatch (BoolType {n = 0}) UnitType))) ==
        "test.fib: Runtime checking: Inferred type is not compatible with expected type; inferred: Bool; expected: Unit")
  ]
