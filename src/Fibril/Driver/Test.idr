-- Bounded pure Bool suites, not IO interpretation or stdout assertions.
module Fibril.Driver.Test

import Fibril.Core.Context
import Fibril.Core.Term
import Fibril.Core.Evaluation
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Driver.Limits
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck
import Fibril.Project.Local
import Fibril.Project.Manifest
import Fibril.Runtime.Path
import Data.List

%default total

testInline : Nat -> String -> IO (Either String (List String))
testInline fuel manifest = do
  loaded <- loadLocalPackageGraph TestPackage manifest
  pure $ do
    graph <- case loaded of Left err => Left (renderGraphError err); Right graph => Right graph
    project <- case checkModuleGraph graph of Left err => Left (renderGraphError err); Right project => Right project
    case checkRuntime checkingDepth typeReductionFuel Empty project.term BoolType of
      Left _ => Left (graph.entry ++ ": Test entry must have main : Bool")
      Right _ => Right ()
    normal <- case normalizeRun fuel project.term of
      OutOfFuel _ => Left (graph.entry ++ ": Test evaluation fuel exhausted (" ++ show fuel ++
                           "); no pass result. Raise it with test --fuel N (0..4096)")
      Normal term => Right term
    case checkRuntime checkingDepth typeReductionFuel Empty normal BoolType of
      Left _ => Left (graph.entry ++ ": Test post-reduction checking failed")
      Right _ => Right ()
    case normal of
      BoolTrue => Right ["Tests: passed (pure Bool suite; bounded reference evaluation)"]
      BoolFalse => Left (graph.entry ++ ": Tests: failed (main returned False)")
      _ => Left (graph.entry ++ ": Test entry did not produce a Bool value")

||| A declared child is an ordinary package, not a source-root override.
||| Require a direct canonical dependency on the parent; do not recursively follow
||| nested test-package declarations. Existing inline suites remain supported.
||| The fuel bounds the reference evaluation of the suite; it is not a time bound.
public export
testPackage : Nat -> String -> IO (Either String (List String))
testPackage fuel manifest = do
  Right parent <- loadLocalInventory manifest | Left err => pure (Left err)
  case parent.entryPackage.manifest.testPackagePath of
    Nothing => testInline fuel manifest
    Just path => do
      checked <- checkLocalPackage manifest
      case checked of
        Left err => pure (Left (renderGraphError err))
        Right _ => do
          let childPath = joinPath (joinPath parent.entryPackage.packageRoot path) "fibril.yaml"
          Right child <- loadLocalInventory childPath | Left err => pure (Left err)
          let parentName = parent.entryPackage.manifest.name
          if child.entryPackage.packageRoot == parent.entryPackage.packageRoot ||
             not (inside parent.entryPackage.packageRoot child.entryPackage.packageRoot)
            then pure (Left "Test package directory must be inside the parent package") else do
           case find (\root => root.manifest.name == parentName) child.packages of
             Nothing => pure (Left "Test package must directly depend on its parent package")
             Just target =>
               if target.manifestPath /= parent.entryPackage.manifestPath ||
                  not (any (\dep => dep.name == parentName) child.entryPackage.manifest.dependencies)
                 then pure (Left "Test package must directly depend on the same canonical parent package")
                 else testInline fuel childPath
