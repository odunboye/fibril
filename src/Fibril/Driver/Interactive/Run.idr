-- Explicit standalone interactive entry points; existing run remains preflighted.
module Fibril.Driver.Interactive.Run

import Fibril.Core.Term
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.Interactive
import Fibril.Driver.Native.Emit
import Fibril.Effect.ConsoleProgram
import Fibril.Runtime.Console
import Fibril.Runtime.ConsoleInput

%default total

||| Standalone interactive defaults: 64 requests, 8192 characters per line.
||| Earlier requests may have happened when a later error is returned.
public export
covering
runInteractiveTerm : Term 0 -> IO (Either String ())
runInteractiveTerm term = case prepareInteractive 128 128 term of
  Left err => pure (Left (show err))
  Right program => do
    result <- runInteractiveConsoleProgram 64 8192 program
    case result of
      Left ConsoleRequestLimit => pure (Left "Interactive request budget exhausted")
      Right (Left err) => pure (Left (show err))
      Right (Right ()) => flushStdout

public export
covering
runInteractiveFile : String -> IO (Either String ())
runInteractiveFile path = do
  loaded <- loadSource path
  case loaded of
    Left err => pure (Left (renderFileError path (show err)))
    Right source => case resolveSource source of
      Left err => pure (Left (renderDriverError path source (FrontendFailure err)))
      Right term => do
        result <- runInteractiveTerm term
        pure $ case result of
          Left err => Left (renderFileError path err)
          Right () => Right ()

||| Emit only; checking and lowering never perform input or output requests.
public export
emitInteractiveCFile : String -> IO (Either String String)
emitInteractiveCFile path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source => case resolveSource source of
      Left err => Left (renderDriverError path source (FrontendFailure err))
      Right term => emitCheckedInteractiveC 64 8192 term
