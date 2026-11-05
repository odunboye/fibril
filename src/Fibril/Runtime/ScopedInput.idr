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

public export
Eq ScopedInputError where
  FileOpenFailed left == FileOpenFailed right = left == right
  FileReadFailed left == FileReadFailed right = left == right
  FileCloseFailed == FileCloseFailed = True
  FileLeaseClosed == FileLeaseClosed = True
  _ == _ = False

-- Export the type, not its constructor or underlying File/IORef. A host caller
-- can retain the wrapper, but cannot retrieve or forge its raw file through this API.
export
data ScopedInput = InputLease (IORef (Maybe File))

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
    Nothing => pure (if explicit then Left FileLeaseClosed else Right ())
    Just handle => do
      writeIORef state Nothing
      closeFileChecked handle

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
    Nothing => pure (Left FileLeaseClosed)
    Just handle => do
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
      state <- newIORef (Just handle)
      pure (Right (InputLease state))

||| Scoped cleanup on all represented callback returns. Escaped wrappers are
||| revoked; arbitrary host exceptions or aborts are not caught. C/Chez only.
||| The callback is trusted host code, not the future source ownership protocol.
export
withScopedInput : String -> (ScopedInput -> IO (Either ScopedInputError value)) ->
                  IO (ResourceOutcome ScopedInputError value)
withScopedInput path body = runResourceScope (acquire path) body (release False)
