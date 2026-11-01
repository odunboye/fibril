-- Checked ordinary reference evaluation; not a compiled runtime or IO interpreter.
module Fibril.Driver.Evaluate

import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Pretty
import Fibril.Core.Reduction
import Fibril.Core.Runtime
import Fibril.Source.File
import Fibril.Driver.Check

%default total

||| Runtime-check source, normalize with a separate budget, then recheck the
||| resulting term against the original type. Neither step is a preservation proof.
||| Type/annotation computation is retained; this is not erased backend execution.
public export
evaluateSource : Nat -> String -> Either String (List String)
evaluateSource fuel source = do
  prepared <- prepareRuntimeSource source
  normal <- case normalize fuel prepared.term of
    OutOfFuel _ => Left "Evaluation budget exhausted; no normal form reported"
    Normal term => Right term
  case checkRuntime 256 128 Empty normal prepared.inferredType of
    Left err => Left ("Post-reduction checking failed: " ++ show err)
    Right _ => Right ["Reference evaluation: normal form (not compiled execution)",
                      "Type: " ++ renderTerm prepared.inferredType,
                      "Normal: " ++ renderTerm normal]

||| Bounded strict source loading precedes all evaluation.
public export
evaluateFile : Nat -> String -> IO (Either String (List String))
evaluateFile fuel path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err => Left (show err)
    Right source => evaluateSource fuel source
