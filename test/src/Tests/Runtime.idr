module Tests.Runtime

import Data.Fin
import Data.Vect
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Usage
import Fibril.Core.Erased

%default total

-- A : Type0, x : A
context : Context 2
context = Extend (Extend Empty Erased (Universe 0)) Linear (Variable FZ)

accepts : Either e a -> Bool
accepts (Right _) = True
accepts _ = False

polyIdentity : Term 0
polyIdentity = Lambda Erased (Universe 0) (Lambda Linear (Variable FZ) (Variable FZ))

||| Runtime regressions distinguish erased acceptance from resource-safe use.
public export
checks : List (String, Bool)
checks =
  [ ("runtime polymorphic identity", accepts (inferRuntime 60 60 Empty polyIdentity))
  , ("runtime linear variable exactly once", accepts (inferRuntime 60 60 context (Variable FZ)))
  , ("runtime linear discard rejected",
      case inferRuntime 60 60 Empty
        (Lambda Erased (Universe 0)
          (Lambda Linear (Variable FZ)
            (Lambda Linear (Variable (FS FZ)) (Variable FZ)))) of
        Left (BoundUsage Linear Erased) => True
        _ => False)
  , ("runtime erased extraction rejected",
      case inferRuntime 60 60
        (Extend (Extend Empty Erased (Universe 0)) Erased (Variable FZ)) (Variable FZ) of
        Left (ContextUsage 0 Erased Linear) => True
        _ => False)
  , ("runtime universe unsupported",
      case inferRuntime 60 60 Empty (Universe 0) of
        Left RuntimeTypeExpression => True
        _ => False)
  , ("runtime type argument allowed when erased",
      accepts (inferRuntime 60 60 context
        (Apply (Apply (weaken (weaken polyIdentity)) (Variable (FS FZ))) (Variable FZ))))
  , ("runtime closure capture preserves usage",
      case inferRuntime 60 60 context
        (Lambda Erased (Universe 0) (Variable (FS FZ))) of
        Right result => result.usage == [Linear, Erased]
        Left _ => False)
  , ("runtime unrestricted argument duplicates linear input",
      case inferRuntime 60 60 context
        (Apply (Lambda Unrestricted (Variable (FS FZ)) (Variable FZ)) (Variable FZ)) of
        Left (ContextUsage 0 Linear Unrestricted) => True
        _ => False)
  , ("runtime duplicated closure captures rejected",
      case inferRuntime 60 60 context
        (Apply
          (Lambda Unrestricted
            (Pi Erased (Universe 0) (Variable (FS (FS FZ)))) (Variable FZ))
          (Lambda Erased (Universe 0) (Variable (FS FZ)))) of
        Left (ContextUsage 0 Linear Unrestricted) => True
        _ => False)
  , ("runtime erased arguments still typechecked",
      case inferRuntime 60 60 Empty (Apply polyIdentity (Universe 0)) of
        Left (TypingError TypeMismatch) => True
        _ => False)
  , ("runtime budget remains explicit",
      case inferRuntime 0 20 Empty polyIdentity of
        Left (TypingError CheckingLimit) => True
        _ => False)
  ]
