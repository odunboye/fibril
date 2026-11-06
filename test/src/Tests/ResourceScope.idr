module Tests.ResourceScope

import Data.IORef
import Data.List
import Fibril.Effect.Resource
import Fibril.Runtime.Resource
import Fibril.Runtime.ScopedInput
import Fibril.Runtime.Console
import Fibril.Effect.ConsoleProgram

%default total

public export
runResourceChecks : IO (List (String, Bool))
runResourceChecks = do
  events <- newIORef (the (List String) [])
  let acquire : IO (Either String ())
      acquire = do modifyIORef events ("acquire" ::); pure (Right ())
  let body : () -> IO (Either String String)
      body _ = do modifyIORef events ("body" ::); pure (Right "value")
  let release : () -> IO (Either String ())
      release _ = do modifyIORef events ("release" ::); pure (Right ())
  success <- runResourceScope acquire body release
  successEvents <- readIORef events
  writeIORef events []
  let failedAcquire : IO (Either String ())
      failedAcquire = do modifyIORef events ("acquire failed" ::); pure (Left "open failed")
  failedOpen <- runResourceScope failedAcquire body release
  openEvents <- readIORef events
  writeIORef events []
  let failedBody : () -> IO (Either String String)
      failedBody _ = do modifyIORef events ("body failed" ::); pure (Left "body error")
  bodyError <- runResourceScope acquire failedBody release
  bodyEvents <- readIORef events
  writeIORef events []
  let failedRelease : () -> IO (Either String ())
      failedRelease _ = do modifyIORef events ("release failed" ::); pure (Left "close error")
  both <- runResourceScope acquire failedBody failedRelease
  bothEvents <- readIORef events
  cleanupOnly <- runResourceScope acquire body failedRelease
  pure [ ("resource scope releases after success",
           case success of
             ResourceFinished (Right "value") (Right ()) =>
               reverse successEvents == ["acquire", "body", "release"]
             _ => False)
       , ("resource scope open failure runs no body or cleanup",
           case failedOpen of
             AcquisitionFailed "open failed" => reverse openEvents == ["acquire failed"]
             _ => False)
       , ("resource scope releases after represented body failure",
           case bodyError of
             ResourceFinished (Left "body error") (Right ()) =>
               reverse bodyEvents == ["acquire", "body failed", "release"]
             _ => False)
       , ("resource scope preserves body and cleanup failures",
           case both of
             ResourceFinished (Left "body error") (Left "close error") =>
               reverse bothEvents == ["acquire", "body failed", "release failed"]
             _ => False)
       , ("resource scope preserves successful value when cleanup fails",
           case cleanupOnly of
             ResourceFinished (Right "value") (Left "close error") => True
             _ => False)
       ]

public export
covering
runScopedInputChecks : String -> IO (List (String, Bool))
runScopedInputChecks path = do
  read <- withScopedInput path (readScopedInput 32)
  readFailure <- withScopedInput path (readScopedInput 2)
  escaped <- withScopedInput path (\lease => pure (Right lease))
  revoked <- case escaped of
    ResourceFinished (Right lease) (Right ()) => do
      result <- readScopedInput 32 lease
      pure (result == Left FileLeaseClosed)
    _ => pure False
  doubleClose <- withScopedInput path (\lease => do
    first <- closeScopedInput lease
    second <- closeScopedInput lease
    pure (Right (first == Right () && second == Left FileLeaseClosed)))
  afterClose <- withScopedInput path (\lease => do
    closed <- closeScopedInput lease
    case closed of
      Left err => pure (Left err)
      Right () => readScopedInput 32 lease)
  called <- newIORef False
  missing <- withScopedInput (path ++ ".missing") (\lease => do
    writeIORef called True
    readScopedInput 32 lease)
  wasCalled <- readIORef called
  (sessionRead, sessionReadCleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left err => pure (Left err)
      Right lease => readScopedInput 32 lease)
  saved <- newIORef (the (Maybe ScopedInput) Nothing)
  (interpreterResult, interpreterCleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left _ => pure Nothing
      Right lease => do
        writeIORef saved (Just lease)
        outcome <- runConsoleProgram 0 (\_ => pure (Right ()))
          (pure (Right Nothing)) (Await (WriteRequest "not executed") (\_ => Finished ()))
        pure (Just outcome))
  captured <- readIORef saved
  closedOnLimit <- the (IO Bool) $ case captured of
    Nothing => pure False
    Just lease => do
      response <- readScopedInput 32 lease
      pure (response == Left FileLeaseClosed)
  (escapedSession, escapedSessionCleanup) <- withInputSession (\session => pure session)
  reopenedSession <- openSessionInput escapedSession path
  (multiple, multipleCleanup) <- withInputSession (\session => do
    first <- openSessionInput session path
    second <- openSessionInput session path
    pure $ case (first, second) of
      (Right left, Right right) => Just (left, right)
      _ => Nothing)
  bothRevoked <- the (IO Bool) $ case multiple of
    Nothing => pure False
    Just (left, right) => do
      first <- readScopedInput 32 left
      second <- readScopedInput 32 right
      pure (first == Left FileLeaseClosed && second == Left FileLeaseClosed)
  (explicitSessionClose, explicitSessionCleanup) <- withInputSession (\session => do
    opened <- openSessionInput session path
    case opened of
      Left err => pure (Left err)
      Right lease => closeScopedInput lease)
  (sessionOpenFailure, sessionOpenCleanup) <- withInputSession (\session =>
    openSessionInput session (path ++ ".missing"))
  pure [ ("input session reads through a registered lease",
           sessionRead == Right (Just "hello") && null sessionReadCleanup)
       , ("input session cleans up after interpreter request exhaustion",
           case interpreterResult of
             Just (Left ConsoleRequestLimit) => closedOnLimit && null interpreterCleanup
             _ => False)
       , ("escaped input session cannot open more files",
           case reopenedSession of
             Left FileSessionClosed => null escapedSessionCleanup
             _ => False)
       , ("input session revokes every registered lease",
           bothRevoked && null multipleCleanup)
       , ("input session does not double-close explicitly closed leases",
           explicitSessionClose == Right () && null explicitSessionCleanup)
       , ("input session acquisition failure adds no cleanup failure",
           case sessionOpenFailure of
             Left (FileOpenFailed _) => null sessionOpenCleanup
             _ => False)
       , ("scoped input reads and closes real file",
           case read of
             ResourceFinished (Right (Just "hello")) (Right ()) => True
             _ => False)
       , ("scoped input closes after represented read failure",
           case readFailure of
             ResourceFinished (Left (FileReadFailed _)) (Right ()) => True
             _ => False)
       , ("scoped input escaped lease cannot access closed file", revoked)
       , ("scoped input rejects double explicit close",
           case doubleClose of
             ResourceFinished (Right True) (Right ()) => True
             _ => False)
       , ("scoped input rejects read after explicit close",
           case afterClose of
             ResourceFinished (Left FileLeaseClosed) (Right ()) => True
             _ => False)
       , ("scoped input open failure skips callback",
           case missing of
             AcquisitionFailed (FileOpenFailed _) => not wasCalled
             _ => False)
       ]
