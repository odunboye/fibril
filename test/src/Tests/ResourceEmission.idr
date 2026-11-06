-- Checked core fixtures for resource emission and hosted/native comparison.
module Tests.ResourceEmission

import Data.Fin
import Data.String
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.ResourceAdmission
import Fibril.Driver.Native.Emit
import Tests.ResourceExecution
import Tests.OwnedRead

%default total

-- Print the first read result, then read with successor ownership and return
-- the second pair to the scope. No old handle survives the pair elimination.
twiceBody : Term 0
twiceBody = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ))
    (IOBind (fileReadResultType (Variable (FS FZ)))
      (fileReadResultType (Variable (FS FZ))) (ReadInputFile (Variable FZ))
      (Lambda Linear (fileReadResultType (Variable (FS FZ)))
        (PairCase
          (Lambda Erased (fileReadResultType (Variable (FS (FS FZ))))
            (IOType (fileReadResultType (Variable (FS (FS (FS FZ)))))))
          (Variable FZ)
          (Lambda Linear (FileHandleType (Variable (FS (FS FZ))))
            (Lambda Linear readResultType
              (IOBind UnitType (fileReadResultType (Variable (FS (FS (FS (FS FZ))))))
                (Apply (weaken (weaken (weaken (weaken (weaken readHandler))))) (Variable FZ))
                (Lambda Linear UnitType
                  (UnitCase (Variable FZ) (ReadInputFile (Variable (FS (FS FZ)))))))))))))

replaceBody : Term 0 -> Term 0 -> Term 0
replaceBody body (IOBind a b (WithInputFile result path _) next) =
  IOBind a b (WithInputFile result path body) next
replaceBody body other = other

-- Normalize only the open-error category: host/platform error wording differs.
normalizeOpenFailure : Term 0 -> Term 0
normalizeOpenFailure (IOBind a b action (Lambda q domain (VariantCase motive value [_ , success, cleanup]))) =
  IOBind a b action (Lambda q domain (VariantCase motive value
    [Lambda Linear StringType
      (BoolCase (StringEqual (Variable FZ) (StringValue ""))
        (WriteLine (StringValue "OPEN_FAILED")) (WriteLine (StringValue "OPEN_FAILED"))),
     success, cleanup]))
normalizeOpenFailure other = other

erasedFirst : Term 0
erasedFirst = PairCase
  (Lambda Erased (Sigma Erased Linear (Universe 0) StringType) (IOType UnitType))
  (PairValue (Sigma Erased Linear (Universe 0) StringType) UnitType (StringValue "kept"))
  (Lambda Erased (Universe 0) (Lambda Linear StringType (WriteLine (Variable FZ))))

erasedSecond : Term 0
erasedSecond = PairCase
  (Lambda Erased (Sigma Linear Erased StringType (Universe 0)) (IOType UnitType))
  (PairValue (Sigma Linear Erased StringType (Universe 0)) (StringValue "kept") UnitType)
  (Lambda Linear StringType (Lambda Erased (Universe 0) (WriteLine (Variable (FS FZ)))))

-- Exercise the recursive emitter added on master inside an acquired scope.
recursiveText : Term 0
recursiveText = NatRec (Lambda Erased NatType StringType) (StringValue "zero")
  (Lambda Erased NatType (Lambda Linear StringType
    (StringAppend (Variable FZ) (StringValue "!")))) (NatSucc NatZero)

runtimeRecursiveText : Term 0
runtimeRecursiveText = NatRecRuntime (Lambda Erased NatType StringType) (StringValue "zero")
  (Lambda Unrestricted NatType (Lambda Linear StringType
    (StringAppend (Variable FZ) (StringValue "!")))) (NatSucc NatZero)

unaryRecursiveText : Term 0
unaryRecursiveText = RecFold
  (Lambda Erased (RecType "scope-rec") StringType) (StringValue "end")
  (Lambda Erased (RecType "scope-rec") (Lambda Linear StringType
    (StringAppend (Variable FZ) (StringValue "+"))))
  (RecMore (RecType "scope-rec") (RecEnd (RecType "scope-rec")))

sequenceRecursiveText : Term 0
sequenceRecursiveText = SeqFold
  (Lambda Erased (SeqType "scope-seq" StringType) StringType) (StringValue "nil")
  (Lambda Linear StringType (Lambda Erased (SeqType "scope-seq" StringType)
    (Lambda Linear StringType (StringAppend (Variable (FS (FS FZ))) (Variable FZ)))))
  (SeqCons (SeqType "scope-seq" StringType) (StringValue "head")
    (SeqNil (SeqType "scope-seq" StringType)))

referenceWrappers : List (String, Term 0 -> Term 0)
referenceWrappers =
  [("NatSucc", NatSucc),
   ("NatRec motive", \x => NatRec x UnitValue UnitValue NatZero),
   ("NatRecRuntime motive", \x => NatRecRuntime x UnitValue UnitValue NatZero),
   ("RecEnd annotation", RecEnd),
   ("RecMore annotation", \x => RecMore x UnitValue),
   ("RecFold motive", \x => RecFold x UnitValue UnitValue UnitValue),
   ("RecCase motive", \x => RecCase x UnitValue UnitValue UnitValue),
   ("SeqType element", SeqType "admission"),
   ("SeqNil annotation", SeqNil),
   ("SeqCons annotation", \x => SeqCons x UnitValue UnitValue),
   ("SeqFold motive", \x => SeqFold x UnitValue UnitValue UnitValue),
   ("SeqCase motive", \x => SeqCase x UnitValue UnitValue UnitValue)]

public export
resourceFixture : String -> String -> Either String (Term 0, Nat)
resourceFixture "read" path = Right (readEntry path, 64)
resourceFixture "plain" path = Right (scopeEntry path returnUnit, 64)
resourceFixture "recursive" path = Right (scopeEntry path (thenReturn (WriteLine recursiveText)), 64)
resourceFixture "recursive-runtime" path = Right (scopeEntry path (thenReturn (WriteLine runtimeRecursiveText)), 64)
resourceFixture "recursive-unary" path = Right (scopeEntry path (thenReturn (WriteLine unaryRecursiveText)), 64)
resourceFixture "recursive-sequence" path = Right (scopeEntry path (thenReturn (WriteLine sequenceRecursiveText)), 64)
resourceFixture "nested" path = Right (scopeEntry path (thenReturn (scopeEntry path returnUnit)), 64)
resourceFixture "twice" path = Right (replaceBody twiceBody (readEntry path), 64)
resourceFixture "write-nul" path = Right (scopeEntry path (thenReturn (WriteLine (StringValue "a\0b"))), 64)
resourceFixture "erased-first" path = Right (erasedFirst, 64)
resourceFixture "erased-second" path = Right (erasedSecond, 64)
resourceFixture "missing" path = Right (normalizeOpenFailure (readEntry (path ++ ".missing")), 64)
resourceFixture "nul" path = Right (normalizeOpenFailure (readEntry (path ++ "\0suffix")), 64)
resourceFixture "budget-before" path = Right (readEntry path, 0)
resourceFixture "budget-body" path = Right (readEntry path, 1)
resourceFixture "budget-after-first" path = Right (replaceBody twiceBody (readEntry path), 3)
resourceFixture _ path = Left "Unknown resource fixture"

public export
checks : List (String, Bool)
checks = map (\(label, wrap) =>
    ("resource admission scans recursive " ++ label,
     containsFileReference (wrap (FileHandleValue 0 0)) &&
     not (containsFileReference (wrap UnitValue)) &&
     emitCheckedResourceC 64 8192 (wrap (FileHandleValue 0 0)) ==
       Left "Native resource entry rejects runtime file references")) referenceWrappers ++
  [ ("resource emitter selects scoped runner and pair lowering",
      case emitCheckedResourceC 64 8192 (scopeEntry "unused" returnUnit) of
        Right code => isInfixOf "fibril_native_resource_run(" code &&
                      isInfixOf "f_with_input(" code && isInfixOf "f_pair(" code
        _ => False)
  , ("resource emitter lowers owned reads and pair elimination",
      case emitCheckedResourceC 64 8192 (readEntry "unused") of
        Right code => isInfixOf "f_read_input(" code && isInfixOf "f_pair_case(" code
        _ => False)
  , ("resource emitter retains first-field erasure",
      case emitCheckedResourceC 64 8192 erasedFirst of
        Right code => isInfixOf "f_pair(r, e, 1, 0," code
        _ => False)
  , ("resource emitter retains second-field erasure",
      case emitCheckedResourceC 64 8192 erasedSecond of
        Right code => isInfixOf "f_pair(r, e, 0, 1," code
        _ => False)
  , ("resource emitter rejects runtime references in erased input syntax",
      emitCheckedResourceC 64 8192
        (Apply (Lambda Erased (FileHandleType (runtimeFileRegion 0)) (IOPure UnitValue))
          (FileHandleValue 0 0)) == Left "Native resource entry rejects runtime file references")
  , ("resource emitter rejects excessive request admission",
      emitCheckedResourceC 100001 8192 (scopeEntry "unused" returnUnit) ==
        Left "Native resource admission limit exceeded")
  , ("resource emitter rejects excessive line admission",
      emitCheckedResourceC 64 8193 (scopeEntry "unused" returnUnit) ==
        Left "Native resource admission limit exceeded")
  , ("resource two-read callback checks with successor ownership",
      case checkRuntime 512 128 Empty twiceBody (scopedInputBodyType readResultType) of
        Right _ => True
        _ => False)
  ]
