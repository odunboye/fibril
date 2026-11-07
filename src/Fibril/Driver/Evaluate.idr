-- Checked ordinary reference evaluation; not a compiled runtime or IO interpreter.
module Fibril.Driver.Evaluate

import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Evaluation
import Fibril.Core.Pretty
import Fibril.Core.Reduction
import Fibril.Core.Runtime
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.Limits
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ModuleGraph

%default total

-- Private: only called after source/project runtime checking. RuntimeSource is
-- raw public data, not a certificate suitable for an unchecked public entrypoint.
evaluatePrepared : Nat -> RuntimeSource -> Either DriverError (List String)
evaluatePrepared fuel prepared = do
  normal <- case normalizeRun fuel prepared.term of
    OutOfFuel _ => Left EvaluationLimit
    Normal term => Right term
  case checkRuntime checkingDepth typeReductionFuel Empty normal prepared.inferredType of
    Left err => Left (PostReductionFailure err)
    Right _ => Right ["Reference evaluation: normal form (not compiled execution)",
                      "Type: " ++ renderType prepared.inferredType,
                      "Normal: " ++ renderTerm normal]

||| Check, normalize, and recheck while preserving structured frontend errors.
||| Type/annotation computation is retained; this is not erased backend execution.
public export
evaluateSourceDetailed : Nat -> String -> Either DriverError (List String)
evaluateSourceDetailed fuel source = do
  prepared <- prepareRuntimeSourceDetailed source
  evaluatePrepared fuel prepared

||| Check the full dependency graph, normalize its entry, then recheck the result.
||| Imported errors retain dependency provenance; result errors are unlocated at entry.
public export
evaluateProjectFile : Nat -> String -> String -> IO (Either String (List String))
evaluateProjectFile fuel root entry = do
  checked <- checkProject root entry
  pure $ case checked of
    Left err => Left (renderGraphError err)
    Right project => case evaluatePrepared fuel (PreparedRuntime project.term project.inferredType) of
      Left err => Left (renderFileError project.graph.entry (show err))
      Right report => Right report

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
