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

executeProject : Nat -> Either GraphError CheckedProject -> IO (Either String ())
executeProject fuel checked =
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => case prepareIO 128 fuel project.term of
      Left err => pure (Left (renderFileError project.graph.entry (show (ConsoleFailure err))))
      Right actions => do
        result <- executeConsoleActions actions
        pure $ case result of
          Left err => Left (renderFileError project.graph.entry err)
          Right () => Right ()

||| Validate all module definitions before preparing any stdout plan.
||| The fuel bounds each reduction while planning output; it is not a time bound.
public export
runProject : Nat -> String -> String -> IO (Either String ())
runProject fuel root entry = checkProject root entry >>= executeProject fuel

public export
runPackage : Nat -> String -> IO (Either String ())
runPackage fuel manifest = checkPackage manifest >>= executeProject fuel

public export
runFile : Nat -> String -> IO (Either String ())
runFile fuel path = do
  loaded <- loadSource path
  case loaded of
    Left err => pure (Left (renderFileError path (show err)))
    Right source => case resolveSource source of
      Left err => pure (Left (renderDriverError path source (FrontendFailure err)))
      Right term => case prepareIO 128 fuel term of
        Left err => pure (Left (renderDriverError path source (ConsoleFailure err)))
        Right actions => do
          result <- executeConsoleActions actions
          pure $ case result of
            Left err => Left (renderFileError path err)
            Right () => Right ()
