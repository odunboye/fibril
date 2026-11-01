-- Checked ordinary reference evaluation; not a compiled runtime or IO interpreter.
module Fibril.Driver.Evaluate

import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Reduction
import Fibril.Core.Runtime
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check

%default total

||| Check, normalize, and recheck while preserving structured frontend errors.
||| Type/annotation computation is retained; this is not erased backend execution.
public export
evaluateSourceDetailed : Nat -> String -> Either DriverError (List String)
evaluateSourceDetailed fuel source = do
  prepared <- prepareRuntimeSourceDetailed source
  normal <- case normalize fuel prepared.term of
    OutOfFuel _ => Left EvaluationLimit
    Normal term => Right term
  case checkRuntime 256 128 Empty normal prepared.inferredType of
    Left err => Left (PostReductionFailure err)
    Right _ => Right ["Reference evaluation: normal form (not compiled execution)",
                      "Type: " ++ renderTerm prepared.inferredType,
                      "Normal: " ++ renderTerm normal]

||| Plain-string presentation preserves the existing source-evaluation API.
||| Neither checking step is a preservation proof.
public export
evaluateSource : Nat -> String -> Either String (List String)
evaluateSource fuel source =
  case evaluateSourceDetailed fuel source of
    Left err => Left (show err)
    Right lines => Right lines

||| Bounded strict loading; located failures render against the original source.
public export
evaluateFile : Nat -> String -> IO (Either String (List String))
evaluateFile fuel path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (renderFileError path (show err))
    Right source =>
      case evaluateSourceDetailed fuel source of
        Left err => Left (renderDriverError path source err)
        Right lines => Right lines
