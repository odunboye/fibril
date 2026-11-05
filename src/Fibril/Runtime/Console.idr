-- Host stdout adapter; never imported by the core normalizer or checkers.
module Fibril.Runtime.Console

import System.File
import Fibril.Effect.Console
import Fibril.Effect.ConsoleProgram

%default total

-- Unlike System.File.fflush, preserve the return code. This is a trusted
-- host adapter for C-compatible backends, not a source-language FFI primitive.
%foreign "C:fflush,libc 6"
primFlush : FilePtr -> PrimIO Int

||| Flush host stdout while preserving its return status.
public export
flushStdout : IO (Either String ())
flushStdout = do
  let FHandle handle = stdout
  status <- primIO (primFlush handle)
  pure $ if status == 0 then Right () else Left "Console stdout flush failed"

||| Execute an explicit console request. Writes can fail or partially complete;
||| validation is separate, not a sandbox/atomic-output or real-time guarantee.
public export
executeConsole : ConsoleAction -> IO (Either String ())
executeConsole (PrintLine text) = do
  result <- fPutStrLn stdout text
  pure $ case result of
    Left err => Left ("Console output failed: " ++ show err)
    Right () => Right ()

||| Sequence host actions left-to-right, stopping on the first represented error.
||| The callback boundary permits deterministic fault-injection tests; it is not
||| a source FFI, an atomic transaction, or a core normalization operation.
public export
sequenceConsole : (ConsoleAction -> IO (Either String ())) ->
                  List ConsoleAction -> IO (Either String ())
sequenceConsole perform [] = pure (Right ())
sequenceConsole perform (action :: rest) = do
  result <- perform action
  case result of
    Left err => pure (Left err)
    Right () => sequenceConsole perform rest

||| Flush once after successful sequencing, including an empty plan. A write
||| failure is returned unchanged and does not trigger this final flush.
||| Separate callbacks make flush errors and ordering deterministically testable.
public export
sequenceConsoleWithFlush : (ConsoleAction -> IO (Either String ())) ->
                           IO (Either String ()) ->
                           List ConsoleAction -> IO (Either String ())
sequenceConsoleWithFlush perform flush actions = do
  result <- sequenceConsole perform actions
  case result of
    Left err => pure (Left err)
    Right () => flush

||| Before a potentially blocking read, make pending prompts visible. A flush
||| failure is returned as the request response and the read is not attempted.
public export
readAfterFlush : IO (Either String ()) -> IO (Either String a) -> IO (Either String a)
readAfterFlush flush read = do
  result <- flush
  case result of
    Left err => pure (Left err)
    Right () => read

||| Request budget exhaustion is distinct from represented operation failures.
public export
data ConsoleProgramError = ConsoleRequestLimit

||| Observed protocol responses, suitable for replay with runScript. Transcripts
||| may contain sensitive input/output; callers decide whether/how to retain them.
public export
record RecordedConsoleResult a where
  constructor RecordedConsole
  outcome : Either ConsoleProgramError a
  transcript : List ConsoleScriptStep

||| Record only requests whose callback was invoked, including represented
||| failures. Retain the observed prefix when request fuel is exhausted. This
||| records protocol behavior, not unrepresented host exceptions or final flush.
public export
recordConsoleProgram : Nat ->
                       (String -> IO (Either String ())) ->
                       IO (Either String (Maybe String)) ->
                       ConsoleProgram a -> IO (RecordedConsoleResult a)
recordConsoleProgram fuel write read (Finished value) =
  pure (RecordedConsole (Right value) [])
recordConsoleProgram Z write read (Await request next) =
  pure (RecordedConsole (Left ConsoleRequestLimit) [])
recordConsoleProgram (S fuel) write read (Await (WriteRequest text) next) = do
  response <- write text
  following <- recordConsoleProgram fuel write read (next response)
  pure (RecordedConsole following.outcome (ExpectWrite text response :: following.transcript))
recordConsoleProgram (S fuel) write read (Await ReadLineRequest next) = do
  response <- read
  following <- recordConsoleProgram fuel write read (next response)
  pure (RecordedConsole following.outcome (SupplyLine response :: following.transcript))

||| Incremental host interpreter. Callbacks can represent failures in their
||| responses; a continuation may recover. No implicit flush is performed.
||| Effects before a fuel limit or later failure cannot be rolled back.
public export
runConsoleProgram : Nat ->
                    (String -> IO (Either String ())) ->
                    IO (Either String (Maybe String)) ->
                    ConsoleProgram a -> IO (Either ConsoleProgramError a)
runConsoleProgram fuel write read (Finished value) = pure (Right value)
runConsoleProgram Z write read (Await request next) = pure (Left ConsoleRequestLimit)
runConsoleProgram (S fuel) write read (Await (WriteRequest text) next) = do
  response <- write text
  runConsoleProgram fuel write read (next response)
runConsoleProgram (S fuel) write read (Await ReadLineRequest next) = do
  response <- read
  runConsoleProgram fuel write read (next response)

||| Production write callback; input remains explicitly unsupported. This
||| interpreter does not replace the existing preflighted source runner.
public export
runOutputConsoleProgram : Nat -> ConsoleProgram a -> IO (Either ConsoleProgramError a)
runOutputConsoleProgram fuel =
  runConsoleProgram fuel (\text => executeConsole (PrintLine text))
                    (pure (Left "Console input is not implemented"))

||| Execute a fully prepared console plan and check stdout flushing. Success
||| does not imply durable storage or atomic output. Validation is the driver's job.
public export
executeConsoleActions : List ConsoleAction -> IO (Either String ())
executeConsoleActions = sequenceConsoleWithFlush executeConsole flushStdout
