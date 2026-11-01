-- Validate a complete restricted console entry before executing any action.
module Fibril.Driver.Run

import Fibril.Core.Term
import Fibril.Source.File
import Fibril.Source.Console
import Fibril.Source.Diagnostic
import Fibril.Effect.Console
import Fibril.Runtime.Console
import Fibril.Driver.Check
import Fibril.Driver.Console

%default total

||| Hosted console execution only, not compilation or ordinary normalization.
||| Invalid source never executes a prefix; output failures can still be partial.
public export
runFile : String -> IO (Either String ())
runFile path = do
  loaded <- loadSource path
  case loaded of
    Left err => pure (Left (renderFileError path (show err)))
    Right source =>
      case prepareSource source of
        Left err => pure (Left (renderDriverError path source (FrontendFailure err)))
        Right (CoreSource _) => pure (Left (renderFileError path
          "run currently requires a main : IO Unit console entry; use eval for ordinary programs"))
        Right (ConsoleSource entry) =>
          case prepareConsole 128 entry of
            Left err => pure (Left (renderDriverError path source (ConsoleFailure err)))
            Right actions => do
              result <- executeConsoleActions actions
              pure $ case result of
                Left err => Left (renderFileError path err)
                Right () => Right ()
