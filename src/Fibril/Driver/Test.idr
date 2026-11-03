-- Bounded pure Bool suites, not IO interpretation or stdout assertions.
module Fibril.Driver.Test

import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Driver.Limits
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck

%default total

public export
testPackage : String -> IO (Either String (List String))
testPackage manifest = do
  loaded <- loadLocalPackageGraph TestPackage manifest
  pure $ do
    graph <- case loaded of Left err => Left (renderGraphError err); Right graph => Right graph
    project <- case checkModuleGraph graph of Left err => Left (renderGraphError err); Right project => Right project
    case checkRuntime checkingDepth typeReductionFuel Empty project.term BoolType of
      Left _ => Left (graph.entry ++ ": Test entry must have main : Bool")
      Right _ => Right ()
    normal <- case normalize 128 project.term of
      OutOfFuel _ => Left (graph.entry ++ ": Test evaluation fuel exhausted (128); no pass result")
      Normal term => Right term
    case checkRuntime checkingDepth typeReductionFuel Empty normal BoolType of
      Left _ => Left (graph.entry ++ ": Test post-reduction checking failed")
      Right _ => Right ()
    case normal of
      BoolTrue => Right ["Tests: passed (pure Bool suite; bounded reference evaluation)"]
      BoolFalse => Left (graph.entry ++ ": Tests: failed (main returned False)")
      _ => Left (graph.entry ++ ": Test entry did not produce a Bool value")
