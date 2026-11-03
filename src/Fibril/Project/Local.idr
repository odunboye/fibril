-- Local manifest closure and canonical roots. No source parsing/checking/fetching.
module Fibril.Project.Local

import Data.List
import Data.List1
import Data.String
import System.Directory
import Fibril.Project.Manifest
import Fibril.Project.Workspace
import Fibril.Runtime.Path
import Fibril.Source.File

%default total

public export
record LocalRoot where
  constructor AdmittedRoot
  manifestPath : String
  packageRoot : String
  sourceRoot : String
  manifest : PackageManifest

public export
record LocalInventory where
  constructor LocalClosure
  entryPackage : LocalRoot
  packages : List LocalRoot
  plan : WorkspacePlan

record Pending where
  constructor Discovering
  packages : List LocalRoot
  edges : Nat

failure : String -> IO (Either String a)
failure = pure . Left

ensureDirectory : String -> IO (Either String ())
ensureDirectory path = do
  Right directory <- openDir path | Left err => pure (Left (path ++ ": " ++ show err))
  closeDir directory
  pure (Right ())

canonicalManifest : String -> IO (Either String (String, String))
canonicalManifest path = do
  Right () <- pure (the (Either String ()) (case reverse (forget (split (== '/') path)) of
    "fibril.yaml" :: _ => Right ()
    _ => Left "Package manifest filename must be exactly fibril.yaml"))
    | Left err => failure err
  Right packageRoot <- exactCanonical (parentPath path) | Left err => failure err
  Right () <- ensureDirectory packageRoot | Left err => failure err
  Right manifestPath <- exactCanonical path | Left err => failure err
  if manifestPath /= joinPath packageRoot "fibril.yaml"
     then failure "Package manifest must be its own exact-case fibril.yaml (no manifest-file symlink alias)"
     else pure (Right (packageRoot, manifestPath))

loadRoot : String -> IO (Either String LocalRoot)
loadRoot path = do
  Right (packageRoot, manifestPath) <- canonicalManifest path | Left err => failure err
  Right source <- loadSourceWithin 8192 manifestPath | Left err => failure (manifestPath ++ ": " ++ show err)
  Right manifest <- pure (decodeManifest manifestPath source) | Left err => failure (manifestPath ++ ": " ++ show err)
  Right sourceRoot <- exactCanonical (joinPath packageRoot manifest.sourceDirectory) | Left err => failure err
  if not (inside packageRoot sourceRoot) then failure "Source root escapes canonical package directory" else do
    Right () <- ensureDirectory sourceRoot | Left err => failure err
    pure (Right (AdmittedRoot manifestPath packageRoot sourceRoot manifest))

asSpec : LocalRoot -> PackageSpec
asSpec root = LocalPackage root.manifest.name root.sourceRoot root.manifest.modulePrefix root.manifest.foundation (map name root.manifest.dependencies)

mutual
  -- Canonical manifest identity deduplicates diamonds. Every incoming key is
  -- checked, including already discovered targets; plans detect dependency cycles.
  discover : Nat -> Maybe String -> String -> Pending -> IO (Either String (LocalRoot, Pending))
  discover Z expected path state = failure "Local package discovery depth exhausted (64)"
  discover (S depth) expected path state = do
    Right (_, canonical) <- canonicalManifest path | Left err => failure err
    case find (\root => root.manifestPath == canonical) state.packages of
      Just root => if expected == Nothing || expected == Just root.manifest.name
                     then pure (Right (root, state)) else failure "Dependency key does not match target package name"
      Nothing => if length state.packages >= 64 then failure "Local package admission exhausted (64)" else do
        Right root <- loadRoot path | Left err => failure err
        if expected /= Nothing && expected /= Just root.manifest.name
           then failure "Dependency key does not match target package name" else do
          if any (\other => other.manifest.name == root.manifest.name) state.packages
             then failure ("Conflicting canonical roots for package " ++ root.manifest.name) else do
            if any (\other => inside root.sourceRoot other.sourceRoot || inside other.sourceRoot root.sourceRoot) state.packages
               then failure "Canonical source roots alias or nest across packages" else do
              let edges = state.edges + length root.manifest.dependencies
              if edges > 256 then failure "Local package edge admission exhausted (256)" else do
                result <- dependencies depth root root.manifest.dependencies (Discovering (root :: state.packages) edges)
                pure (map (\next => (root, next)) result)

  dependencies : Nat -> LocalRoot -> List PathDependency -> Pending -> IO (Either String Pending)
  dependencies depth root [] state = pure (Right state)
  dependencies depth root (dep :: rest) state = do
    let path = joinPath (joinPath root.packageRoot dep.path) "fibril.yaml"
    Right (_, next) <- discover depth (Just dep.name) path state | Left err => failure err
    dependencies depth root rest next

||| Only the explicit root's dependency closure, not workspace-member discovery.
||| Directory/source roots are canonical, exact-case and non-overlapping. This
||| is admission metadata, not an immutable snapshot, sandbox or typing authority.
public export
loadLocalInventory : String -> IO (Either String LocalInventory)
loadLocalInventory path = do
  Right (entry, complete) <- discover 64 Nothing path (Discovering [] 0) | Left err => failure err
  pure $ do
    plan <- case planWorkspace (map asSpec complete.packages) of
      Left err => Left (show err)
      Right plan => Right plan
    Right (LocalClosure entry complete.packages plan)
