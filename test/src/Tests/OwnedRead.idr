module Tests.OwnedRead

import Data.Fin
import Data.List
import Data.IORef
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Erased
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Driver.Resource
import Fibril.Runtime.ScopedInput
import Fibril.Runtime.InputOwnership

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 512 128 Empty term ty of
  Right _ => True
  Left _ => False

readBody : Term 0
readBody = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ)) (ReadInputFile (Variable FZ)))

readHandler : Term 0
readHandler = Lambda Linear readResultType
  (VariantCase (Lambda Erased readResultType (IOType UnitType)) (Variable FZ)
    [WriteLine (StringValue "EOF"),
     Lambda Linear StringType (WriteLine (Variable FZ)),
     Lambda Linear StringType (WriteLine (Variable FZ))])

readEntry : String -> Term 0
readEntry path = IOBind (fileScopeResultType readResultType) UnitType
  (WithInputFile readResultType (StringValue path) readBody)
  (Lambda Linear (fileScopeResultType readResultType)
    (VariantCase (Lambda Erased (fileScopeResultType readResultType) (IOType UnitType)) (Variable FZ)
      [Lambda Linear StringType (WriteLine (Variable FZ)),
       weaken readHandler,
       Lambda Linear (Sigma Linear Linear readResultType StringType)
         (PairCase (Lambda Erased (Sigma Linear Linear readResultType StringType) (IOType UnitType))
           (Variable FZ)
           (Lambda Linear readResultType (Lambda Linear StringType
             (IOBind UnitType UnitType (Apply (weaken (weaken (weaken (weaken readHandler)))) (Variable (FS FZ)))
               (Lambda Linear UnitType (UnitCase (Variable FZ) (WriteLine (Variable (FS FZ)))))))))]))

public export
checks : List (String, Bool)
checks =
  [ ("file read callback returns successor ownership with its result",
      accepted readBody (scopedInputBodyType readResultType))
  , ("file read rejects a non-handle argument",
      case inferErased 128 128 Empty (ReadInputFile UnitValue) of
        Left (ExpectedFileHandle _) => True
        _ => False)
  , ("file read normalization stays inert",
      case normalize 0 (the (Term 0) (ReadInputFile (FileHandleValue 0 0))) of
        Normal value => sameSyntax value (ReadInputFile (FileHandleValue 0 0))
        _ => False)
  , ("file reference generations retain type but not value identity",
      accepted (FileHandleValue 0 0) (FileHandleType (runtimeFileRegion 0)) &&
      accepted (FileHandleValue 0 1) (FileHandleType (runtimeFileRegion 0)) &&
      not (sameSyntax (the (Term 0) (FileHandleValue 0 0)) (FileHandleValue 0 1)))
  , ("file read cannot share ownership with the original handle",
      let pair : Term 1
          pair = Sigma Linear Linear (IOType (fileReadResultType UnitType)) (FileHandleType UnitType)
          term = Lambda Linear (FileHandleType UnitType)
            (PairValue pair (ReadInputFile (Variable FZ)) (Variable FZ))
          ty = Pi Linear (FileHandleType UnitType) pair in
        (case checkErased 512 128 Empty term ty of Right () => True; _ => False) &&
        not (accepted term ty))
  , ("file-reading scope can form a checked IO Unit program",
      accepted (readEntry "not opened by checking") (IOType UnitType))
  ]

public export
covering
runOwnedReadChecks : String -> IO (List (String, Bool))
runOwnedReadChecks path = do
  (tableChecks, cleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left _ => pure [("ownership-table fixture opens", False)]
      Right lease => do
        table <- newInputOwnershipTable
        unknown <- readOwnedInput 32 table 99 0
        identity <- registerInputOwnership table lease
        first <- readOwnedInput 32 table identity 0
        stale <- readOwnedInput 32 table identity 0
        oldReturn <- checkInputOwnership table identity 0
        second <- readOwnedInput 32 table identity 1
        liveReturn <- checkInputOwnership table identity 2
        revokeInputOwnership table identity
        revoked <- readOwnedInput 32 table identity 2
        pure [ ("ownership table rejects unknown references", unknown == Left UnknownInputReference)
             , ("owned file read advances the generation", first == Right (1, Right (Just "hello")))
             , ("ownership table rejects stale reads", stale == Left StaleInputReference)
             , ("scope ownership return rejects an old generation", oldReturn == Left StaleInputReference)
             , ("stale read does not consume input", second == Right (2, Right (Just "")))
             , ("scope ownership return accepts the current generation", liveReturn == Right ())
             , ("ownership table rejects revoked reads", revoked == Left RevokedInputReference)
             ])
  (errorChecks, errorCleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left _ => pure [("owned read-error fixture opens", False)]
      Right lease => do
        table <- newInputOwnershipTable
        identity <- registerInputOwnership table lease
        failed <- readOwnedInput 2 table identity 0
        current <- checkInputOwnership table identity 1
        recovered <- readOwnedInput 32 table identity 1
        pure [ ("represented file-read error still returns successor ownership",
                  case failed of
                    Right (1, Left (FileReadFailed _)) => current == Right ()
                    _ => False)
             , ("ownership permits continued reads after a represented read error",
                  recovered == Right (2, Right (Just "")))
             ])
  (eofChecks, eofCleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left _ => pure [("owned EOF fixture opens", False)]
      Right lease => do
        table <- newInputOwnershipTable
        identity <- registerInputOwnership table lease
        _ <- readOwnedInput 32 table identity 0
        _ <- readOwnedInput 32 table identity 1
        _ <- readOwnedInput 32 table identity 2
        _ <- readOwnedInput 32 table identity 3
        eof <- readOwnedInput 32 table identity 4
        current <- checkInputOwnership table identity 5
        pure [("EOF returns successor file ownership", eof == Right (5, Right Nothing) && current == Right ())])
  (closedChecks, closedCleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left _ => pure [("owned revoked-lease fixture opens", False)]
      Right lease => do
        table <- newInputOwnershipTable
        identity <- registerInputOwnership table lease
        _ <- closeScopedInput lease
        read <- readOwnedInput 32 table identity 0
        current <- checkInputOwnership table identity 1
        pure [("owned read revokes a physically closed lease",
               read == Left RevokedInputReference && current == Left RevokedInputReference)])
  writes <- newIORef (the (List String) [])
  leases <- newIORef (the (List ScopedInput) [])
  let host = ResourceHost
        (\text => do modifyIORef writes (text ::); pure (Right ()))
        (pure (Left "stdin unused")) (pure (Right ()))
        (\_, lease => modifyIORef leases (lease ::))
  executed <- runResourceTermWith 128 128 64 host (readEntry path)
  output <- readIORef writes
  observed <- readIORef leases
  closed <- case observed of
    [lease] => do
      result <- readScopedInput 32 lease
      pure (result == Left FileLeaseClosed)
    _ => pure False
  writeIORef writes []
  writeIORef leases []
  emptyExecuted <- runResourceTermWith 128 128 64 host (readEntry (path ++ ".empty"))
  emptyOutput <- readIORef writes
  writeIORef writes []
  longExecuted <- runResourceTermWith 128 128 64 host (readEntry (path ++ ".long"))
  longOutput <- readIORef writes
  pure (tableChecks ++ errorChecks ++ eofChecks ++ closedChecks ++
    [("owned read table fixtures close without cleanup failure",
       null cleanup && null errorCleanup && null eofCleanup && null closedCleanup),
     ("checked scope returns EOF with ownership and closes",
       case emptyExecuted.outcome of
         Right () => emptyOutput == ["EOF"] && null emptyExecuted.cleanupFailures
         _ => False),
     ("checked scope handles overlong read as a value and closes",
       case longExecuted.outcome of
         Right () => longOutput == ["File read failed: Console input line length limit exceeded"] &&
           null longExecuted.cleanupFailures
         _ => False),
     ("checked scope reads a file, returns successor ownership and closes",
       case executed.outcome of
         Right () => output == ["hello"] && closed && null executed.cleanupFailures
         _ => False)])
