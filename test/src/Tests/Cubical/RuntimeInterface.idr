module Tests.Cubical.RuntimeInterface

import Data.Fin
import Fibril.Core.Quantity
import Fibril.Core.Term
import Fibril.Cubical.RuntimeInterface

%default total

arrow : Quantity -> Term 0
arrow q = Pi q UnitType BoolType

accepted : Nat -> Term n -> Bool
accepted budget term = case admitRuntimeInterface budget term of
  Right _ => True
  Left _ => False

limited : Either InterfaceError a -> Bool
limited (Left InterfaceLimit) = True
limited _ = False

unsupported : Either InterfaceError a -> Bool
unsupported (Left UnsupportedInterface) = True
unsupported _ = False

same : Nat -> Term n -> Term m -> Bool -> Bool
same budget left right expected = case compareRuntimeInterfaces budget left right of
  Right actual => actual == expected
  Left _ => False

export
checks : List (String, Bool)
checks =
  [ ("interface literal admission has exact shared node boundary",
      not (accepted 2 (arrow Linear)) && accepted 3 (arrow Linear))
  , ("interface comparison shares admission and comparison allowance",
      limited (compareRuntimeInterfaces 8 (arrow Linear) (arrow Linear)) &&
      same 9 (arrow Linear) (arrow Linear) True)
  , ("interface comparison distinguishes retained base types",
      same 3 (the (Term 0) UnitType) (the (Term 0) BoolType) False)
  , ("interface comparison preserves all binder quantities",
      same 9 (arrow Erased) (arrow Linear) False &&
      same 9 (arrow Linear) (arrow Unrestricted) False &&
      same 9 (arrow Erased) (arrow Unrestricted) False)
  , ("interface admission rejects a dependent codomain",
      unsupported (admitRuntimeInterface 10
        (the (Term 0) (Pi Linear UnitType (Variable FZ)))))
  , ("interface admission rejects outer context variables too",
      unsupported (admitRuntimeInterface 10 (the (Term 1) (Variable FZ))))
  , ("interface admission rejects handle families and internal references",
      unsupported (admitRuntimeInterface 10 (the (Term 0) (FileHandleType UnitType))) &&
      unsupported (admitRuntimeInterface 10 (the (Term 0) (FileHandleValue 0 0))))
  , ("interface admission rejects effects and erased boxes",
      unsupported (admitRuntimeInterface 10 (the (Term 0) (IOType UnitType))) &&
      unsupported (admitRuntimeInterface 10 (the (Term 0) (BoxType Erased BoolType))))
  , ("interface comparison admits both inputs before deciding mismatch",
      unsupported (compareRuntimeInterfaces 20 (the (Term 0) UnitType)
        (Pi Erased UnitType (the (Term 1) (FileHandleValue 0 0)))))
  , ("interface admission never normalizes unsupported beta wrappers",
      unsupported (admitRuntimeInterface 10
        (the (Term 0) (Apply (Lambda Erased UnitType BoolType) UnitValue))))
  , ("interface zero allowance cannot admit a literal",
      limited (admitRuntimeInterface 0 (the (Term 0) BoolType)))
  , ("interface nested arrows share rather than reset allowance",
      not (accepted 4 (the (Term 0) (Pi Linear (arrow Erased) BoolType))) &&
      accepted 5 (the (Term 0) (Pi Linear (arrow Erased) BoolType)))
  ]
