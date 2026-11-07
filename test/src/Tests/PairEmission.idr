module Tests.PairEmission

import Data.Fin
import Data.List
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Driver.Native.Emit
import Tests.ResourceExecution

%default total

public export
emitters : List (String, Term 0 -> Either String String)
emitters = [("preflight", emitCheckedC),
            ("interactive", emitCheckedInteractiveC 64 8192),
            ("resources", emitCheckedResourceC 64 8192),
            ("binary", emitCheckedBinaryC 64 8192)]

-- Raw checked-core evidence, separate from the source record fixtures.
public export
pairEntry : Quantity -> Quantity -> Term 0
pairEntry q r =
  let ty = Sigma q r UnitType UnitType
      body = if r == Erased then IOPure UnitValue
             else UnitCase (Variable FZ) (IOPure UnitValue)
      body = if q == Erased then body
             else UnitCase (Variable (FS FZ)) body in
    PairCase (Lambda Erased ty (IOType UnitType))
      (PairValue ty UnitValue UnitValue)
      (Lambda q UnitType (Lambda r UnitType body))

-- These are deliberately raw (sometimes ill-typed) syntax: the exact admission
-- diagnostic establishes that whole-syntax scanning still precedes checking.
wrappers : List (Term 0 -> Term 0)
wrappers =
  [\x => PairValue x UnitValue UnitValue,
   \x => PairValue (Sigma Erased Linear UnitType UnitType) x UnitValue,
   \x => PairValue (Sigma Linear Erased UnitType UnitType) UnitValue x,
   \x => PairCase x UnitValue UnitValue,
   \x => PairCase UnitValue UnitValue (BoolCase BoolTrue (IOPure UnitValue) x),
   \x => PairValue (Sigma Erased Linear x UnitType) UnitValue UnitValue]

expect : String -> Either String String -> Bool
expect message (Left error) = message == error
expect _ _ = False

public export
checks : List (String, Bool)
checks =
  [("old modes scan forbidden binary capabilities inside pairs before typing",
    all (\wrap => all (\emit => expect "Binary IO requires the explicit binary runner" (emit (wrap FlushBytes)))
      [emitCheckedC, emitCheckedInteractiveC 64 8192, emitCheckedResourceC 64 8192]) wrappers),
   ("binary scans forbidden text and resources inside pairs before typing",
    all (\wrap => all (\capability => expect "Native binary entry rejects non-binary IO/references"
      (emitCheckedBinaryC 64 8192 (wrap capability)))
      [ReadLine, WriteLine (StringValue "hidden"), FileHandleType UnitType,
       FileHandleValue 0 0, ReadInputFile UnitValue, WithInputFile UnitType UnitValue UnitValue]) wrappers),
   ("resources scan raw references inside pairs before typing",
    all (\wrap => expect "Native resource entry rejects runtime file references"
      (emitCheckedResourceC 64 8192 (wrap (FileHandleValue 0 0)))) wrappers),
   ("pure pair lowering does not grant scoped-resource permission",
    all (\emit => expect "C backend does not support this computational core construct"
      (emit (BoolCase BoolTrue (IOPure UnitValue) (scopeEntry "unused" returnUnit))))
      [emitCheckedC, emitCheckedInteractiveC 64 8192])]
