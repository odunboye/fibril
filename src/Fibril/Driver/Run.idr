-- Check ordinary main : IO Unit, prepare all requests, then perform host IO.
module Fibril.Driver.Run

import Fibril.Core.Term
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Effect.Console
import Fibril.Runtime.Console
import Fibril.Driver.Check
import Fibril.Driver.Console

%default total

public export
runFile : String -> IO (Either String ())
runFile path = do
  loaded <- loadSource path
  case loaded of
    Left err => pure (Left (renderFileError path (show err)))
    Right source => case resolveSource source of
      Left err => pure (Left (renderDriverError path source (FrontendFailure err)))
      Right term => case prepareIO 128 128 term of
        Left err => pure (Left (renderDriverError path source (ConsoleFailure err)))
        Right actions => do
          result <- executeConsoleActions actions
          pure $ case result of
            Left err => Left (renderFileError path err)
            Right () => Right ()
