module Tests.ResourceExecution

import Data.Fin
import Data.List
import Data.IORef
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Driver.Resource
import Fibril.Runtime.ScopedInput

%default total

public export
returnUnit : Term 0
returnUnit = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ))
    (IOPure (PairValue
      (Sigma Linear Linear (FileHandleType (Variable (FS FZ))) UnitType)
      (Variable FZ) UnitValue)))

public export
scopeEntry : String -> Term 0 -> Term 0
scopeEntry path body = IOBind (fileScopeResultType UnitType) UnitType
  (WithInputFile UnitType (StringValue path) body)
  (Lambda Linear (fileScopeResultType UnitType)
    (VariantCase (Lambda Erased (fileScopeResultType UnitType) (IOType UnitType)) (Variable FZ)
      [Lambda Linear StringType (WriteLine (Variable FZ)),
       Lambda Linear UnitType (UnitCase (Variable FZ) (IOPure UnitValue)),
       Lambda Linear (Sigma Linear Linear UnitType StringType)
         (PairCase (Lambda Erased (Sigma Linear Linear UnitType StringType) (IOType UnitType))
           (Variable FZ)
           (Lambda Linear UnitType (Lambda Linear StringType
             (UnitCase (Variable (FS FZ)) (WriteLine (Variable FZ))))))]))

-- Run a closed IO Unit action, then return the still-owned outer handle.
public export
thenReturn : Term 0 -> Term 0
thenReturn action = Lambda Erased (Universe 0)
  (Lambda Linear (FileHandleType (Variable FZ))
    (IOBind UnitType
      (Sigma Linear Linear (FileHandleType (Variable (FS FZ))) UnitType)
      (weaken (weaken action))
      (Lambda Linear UnitType
        (UnitCase (Variable FZ)
          (IOPure (PairValue
            (Sigma Linear Linear (FileHandleType (Variable (FS (FS FZ)))) UnitType)
            (Variable (FS FZ)) UnitValue))))))

covering
allClosed : List ScopedInput -> IO Bool
allClosed [] = pure True
allClosed (lease :: rest) = do
  response <- readScopedInput 32 lease
  following <- allClosed rest
  pure (response == Left FileLeaseClosed && following)

successful : ResourceExecution -> Bool
successful result = case result.outcome of
  Right () => null result.cleanupFailures
  Left _ => False

public export
covering
runResourceExecutionChecks : String -> IO (List (String, Bool))
runResourceExecutionChecks path = do
  leases <- newIORef (the (List ScopedInput) [])
  identities <- newIORef (the (List Nat) [])
  writes <- newIORef (the (List String) [])
  flushes <- newIORef Z
  let observe : Nat -> ScopedInput -> IO ()
      observe identity lease = do
        modifyIORef leases (lease ::)
        modifyIORef identities (identity ::)
  let write : String -> IO (Either String ())
      write text = do modifyIORef writes (text ::); pure (Right ())
  let flush : IO (Either String ())
      flush = do modifyIORef flushes S; pure (Right ())
  let host = ResourceHost write (pure (Left "stdin unused")) flush observe
  let clear : IO ()
      clear = do writeIORef leases []; writeIORef identities []; writeIORef writes []; writeIORef flushes Z
  normal <- runResourceTermWith 128 128 64 host (scopeEntry path returnUnit)
  normalLeases <- readIORef leases
  normalClosed <- allClosed normalLeases
  normalFlushes <- readIORef flushes
  clear
  let writesThenReturns = thenReturn (WriteLine (StringValue "inside"))
  limited <- runResourceTermWith 128 128 1 host (scopeEntry path writesThenReturns)
  limitedLeases <- readIORef leases
  limitedClosed <- allClosed limitedLeases
  limitedWrites <- readIORef writes
  clear
  let failWrite : String -> IO (Either String ())
      failWrite text = do modifyIORef writes (text ::); pure (Left "write failed")
  let failedHost = ResourceHost failWrite (pure (Left "stdin unused")) flush observe
  failed <- runResourceTermWith 128 128 64 failedHost (scopeEntry path writesThenReturns)
  failedLeases <- readIORef leases
  failedClosed <- allClosed failedLeases
  clear
  missing <- runResourceTermWith 128 128 64 host (scopeEntry (path ++ ".missing") writesThenReturns)
  missingLeases <- readIORef leases
  missingWrites <- readIORef writes
  clear
  zero <- runResourceTermWith 128 128 0 host (scopeEntry path returnUnit)
  zeroLeases <- readIORef leases
  clear
  nested <- runResourceTermWith 128 128 64 host
    (scopeEntry path (thenReturn (scopeEntry path returnUnit)))
  nestedLeases <- readIORef leases
  nestedClosed <- allClosed nestedLeases
  nestedIdentities <- readIORef identities
  clear
  let earlyClose : Nat -> ScopedInput -> IO ()
      earlyClose identity lease = do
        observe identity lease
        _ <- closeScopedInput lease
        pure ()
  let prematurelyClosed = ResourceHost failWrite (pure (Left "stdin unused")) flush earlyClose
  both <- runResourceTermWith 128 128 64 prematurelyClosed (scopeEntry path writesThenReturns)
  clear
  -- Even erased syntax may not inject a pre-existing runtime reference.
  let injected = Apply
        (Lambda Erased (FileHandleType (runtimeFileRegion 0)) (IOPure UnitValue))
        (FileHandleValue 0 0)
  rejected <- runResourceTermWith 128 128 64 host injected
  rejectedLeases <- readIORef leases
  clear
  let cleanupStateError = ResourceHost write (pure (Left "stdin unused")) flush earlyClose
  cleanupHandled <- runResourceTermWith 128 128 64 cleanupStateError (scopeEntry path returnUnit)
  cleanupWrites <- readIORef writes
  clear
  depthLimited <- runResourceTermWith 2 128 64 host (scopeEntry path returnUnit)
  depthLeases <- readIORef leases
  depthClosed <- allClosed depthLeases
  clear
  nulPath <- runResourceTermWith 128 128 64 host (scopeEntry (path ++ "\0suffix") returnUnit)
  nulLeases <- readIORef leases
  nulWrites <- readIORef writes
  pure [ ("resource path rejects embedded NUL before acquiring a lease",
           successful nulPath && nulPath.regionsCreated == 0 && null nulLeases &&
           nulWrites == ["File open failed: NUL in path"])
       , ("checked resource scope closes before ownership return on depth exhaustion",
           case depthLimited.outcome of
             Left ResourceDepthLimit => depthClosed && length depthLeases == 1 &&
               null depthLimited.cleanupFailures
             _ => False)
       , ("checked resource scope opens, returns ownership and closes",
           successful normal && normal.regionsCreated == 1 &&
           length normalLeases == 1 && normalClosed && normalFlushes == 1)
       , ("checked resource scope closes after request exhaustion",
           case limited.outcome of
             Left ResourceRequestLimit => limitedClosed && length limitedLeases == 1 &&
               null limitedWrites && null limited.cleanupFailures
             _ => False)
       , ("checked resource scope closes after represented output failure",
           case failed.outcome of
             Left (ResourceWriteFailure "write failed") =>
               failedClosed && length failedLeases == 1 && null failed.cleanupFailures
             _ => False)
       , ("checked resource open failure skips body and returns an error value",
           successful missing && missing.regionsCreated == 0 && null missingLeases &&
           length missingWrites == 1 && not (elem "inside" missingWrites))
       , ("checked resource request exhaustion prevents acquisition",
           case zero.outcome of
             Left ResourceRequestLimit => null zeroLeases && zero.regionsCreated == 0
             _ => False)
       , ("checked nested resource scopes use distinct regions and close both leases",
           successful nested && nested.regionsCreated == 2 && nestedClosed &&
           reverse nestedIdentities == [0, 1] && length nestedLeases == 2)
       , ("checked resource primary and cleanup-state failures are preserved",
           case both.outcome of
             Left (ResourceCleanupFailure (ResourceWriteFailure "write failed") FileLeaseClosed) => True
             _ => False)
       , ("resource admission rejects runtime references even in erased arguments",
           case rejected.outcome of
             Left ResourceAdmission => null rejectedLeases && rejected.regionsCreated == 0
             _ => False)
       , ("checked resource cleanup-state error reaches the result handler",
           successful cleanupHandled && cleanupWrites == ["File lease is closed"])
       ]
