-- Check ordinary main : IO Unit, prepare all requests, then perform host IO.
module Fibril.Driver.Run

import Fibril.Core.Term
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Effect.Console
import Fibril.Runtime.Console
import Fibril.Driver.Check
import Fibril.Driver.Console
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default total

||| Validate all module definitions before preparing any stdout plan.
public export
runProject : String -> String -> IO (Either String ())
runProject root entry = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => case prepareIO 128 128 project.term of
      Left err => pure (Left (renderFileError project.graph.entry (show (ConsoleFailure err))))
      Right actions => do
        result <- executeConsoleActions actions
        pure $ case result of
          Left err => Left (renderFileError project.graph.entry err)
          Right () => Right ()

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
