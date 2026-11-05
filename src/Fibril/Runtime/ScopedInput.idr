-- Host-only scoped file pilot. No source primitives or core constructors.
module Fibril.Runtime.ScopedInput

import Data.IORef
import System.File
import Fibril.Effect.Resource
import Fibril.Runtime.Resource
import Fibril.Runtime.ConsoleInput

%default total

public export
data ScopedInputError
  = FileOpenFailed String
  | FileReadFailed String
  | FileCloseFailed
  | FileLeaseClosed
  | FileSessionClosed

public export
Show ScopedInputError where
  show (FileOpenFailed message) = "File open failed: " ++ message
  show (FileReadFailed message) = "File read failed: " ++ message
  show FileCloseFailed = "File close failed"
  show FileLeaseClosed = "File lease is closed"
  show FileSessionClosed = "File session is closed"

public export
Eq ScopedInputError where
  FileOpenFailed left == FileOpenFailed right = left == right
  FileReadFailed left == FileReadFailed right = left == right
  FileCloseFailed == FileCloseFailed = True
  FileLeaseClosed == FileLeaseClosed = True
  FileSessionClosed == FileSessionClosed = True
  _ == _ = False

-- Export the type, not its constructor or underlying File/IORef. A host caller
-- can retain the wrapper, but cannot retrieve or forge its raw file through this API.
data LeaseState = LeaseOpen File | LeaseClosed (Either ScopedInputError ())

export
data ScopedInput = InputLease (IORef LeaseState)

%foreign "C:fclose,libc 6"
primClose : FilePtr -> PrimIO Int

closeFileChecked : File -> IO (Either ScopedInputError ())
closeFileChecked (FHandle handle) = do
  status <- primIO (primClose handle)
  pure $ if status == 0 then Right () else Left FileCloseFailed

-- Revoke before closing, even if fclose fails. Do not retry an indeterminate
-- close: the underlying descriptor may already have been released/reused.
release : Bool -> ScopedInput -> IO (Either ScopedInputError ())
release explicit (InputLease state) = do
  current <- readIORef state
  case current of
    LeaseClosed previous => pure (if explicit then Left FileLeaseClosed else previous)
    LeaseOpen handle => do
      writeIORef state (LeaseClosed (Right ()))
      result <- closeFileChecked handle
      writeIORef state (LeaseClosed result)
      pure result

||| Explicit close is allowed within the scope. A second explicit close fails;
||| scope cleanup recognizes successful transfer to the closed state.
export
closeScopedInput : ScopedInput -> IO (Either ScopedInputError ())
closeScopedInput = release True

||| Sequential host-only access. No thread safety or linear typing is claimed.
||| Borrowed wrapper lifetime is checked before touching the underlying file.
export
covering
readScopedInput : Nat -> ScopedInput -> IO (Either ScopedInputError (Maybe String))
readScopedInput limit (InputLease state) = do
  current <- readIORef state
  case current of
    LeaseClosed _ => pure (Left FileLeaseClosed)
    LeaseOpen handle => do
      result <- readConsoleLine limit handle
      pure $ case result of
        Left err => Left (FileReadFailed err)
        Right line => Right line

acquire : String -> IO (Either ScopedInputError ScopedInput)
acquire path = do
  opened <- openFile path Read
  case opened of
    Left err => pure (Left (FileOpenFailed (show err)))
    Right handle => do
      state <- newIORef (LeaseOpen handle)
      pure (Right (InputLease state))

||| Scoped cleanup on all represented callback returns. Escaped wrappers are
||| revoked; arbitrary host exceptions or aborts are not caught. C/Chez only.
||| The callback is trusted host code, not the future source ownership protocol.
export
withScopedInput : String -> (ScopedInput -> IO (Either ScopedInputError value)) ->
                  IO (ResourceOutcome ScopedInputError value)
withScopedInput path body = runResourceScope (acquire path) body (release False)

||| Opaque per-execution registry. New leases are retained until session cleanup,
||| even if a body never returns their ownership token through its normal path.
export
data InputSession = Session (IORef (Maybe (List ScopedInput)))

||| Register ownership immediately on successful open. No raw file escapes.
||| Session use is sequential; this is not a concurrent/atomic resource registry.
export
openSessionInput : InputSession -> String -> IO (Either ScopedInputError ScopedInput)
openSessionInput (Session state) path = do
  current <- readIORef state
  case current of
    Nothing => pure (Left FileSessionClosed)
    Just leases => do
      opened <- acquire path
      case opened of
        Left err => pure (Left err)
        Right lease => do
          writeIORef state (Just (lease :: leases))
          pure (Right lease)

cleanupLeases : List ScopedInput -> IO (List ScopedInputError)
cleanupLeases [] = pure []
cleanupLeases (lease :: rest) = do
  result <- release False lease
  following <- cleanupLeases rest
  pure $ case result of
    Left err => err :: following
    Right () => following

||| Final cleanup covers any represented callback result, including interpreter
||| failure before normal ownership return. Revoke the session before closing
||| leases, newest first. Preserve the primary result and every cleanup failure.
||| Backend exceptions, nontermination and process termination are not caught.
export
withInputSession : (InputSession -> IO value) -> IO (value, List ScopedInputError)
withInputSession body = do
  state <- newIORef (Just [])
  result <- body (Session state)
  current <- readIORef state
  writeIORef state Nothing
  errors <- cleanupLeases (maybe [] id current)
  pure (result, errors)
