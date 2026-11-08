-- Local manifest closure and canonical roots. No source parsing/checking/fetching.
module Fibril.Project.Local

import Data.List
import Data.List1
import Data.String
import System.Directory
import System.File
import Fibril.Project.Digest
import Fibril.Project.Lock
import Fibril.Project.LockDecode
import Fibril.Project.Manifest
import Fibril.Project.Workspace
import Fibril.Runtime.Path
import Fibril.Runtime.Project
import Fibril.Source.File
import Fibril.Source.UTF8

%default total

public export
record LocalRoot where
  constructor AdmittedRoot
  manifestPath : String
  manifestText : String
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
    pure (Right (AdmittedRoot manifestPath source packageRoot sourceRoot manifest))

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
loadUnlockedInventory : String -> IO (Either String LocalInventory)
loadUnlockedInventory path = do
  Right (entry, complete) <- discover 64 Nothing path (Discovering [] 0) | Left err => failure err
  pure $ do
    plan <- case planWorkspace (map asSpec complete.packages) of
      Left err => Left (show err)
      Right plan => Right plan
    Right (LocalClosure entry complete.packages plan)

-- fibril.lock (docs/lockfile.md): change detection for local packages, not a pin
-- and not authenticity. Raw source bytes are the UTF-8 re-encoding of the strictly
-- decoded text, which is lossless, so a CRLF checkout changes the digest.

bytesOf : String -> Either String (List Bits8)
bytesOf text = case encodeUTF8 text of
  Left err => Left (show err)
  Right bytes => Right bytes

readBytes : String -> IO (Either String (List Bits8))
readBytes path = do
  Right text <- loadSource path | Left err => failure (path ++ ": " ++ show err)
  pure (bytesOf text)

isDirectoryPath : String -> IO Bool
isDirectoryPath path = do
  Right directory <- openDir path | Left _ => pure False
  closeDir directory
  pure True

mutual
  -- Only directories and *.fib files are followed, and each must be its own exact
  -- canonical path, so any symlink or alias in the tree is rejected, not followed.
  walkSources : Nat -> String -> String -> IO (Either String (List (String, List Bits8)))
  walkSources Z dir rel = failure "Package source tree is nested too deeply (16)"
  walkSources (S depth) dir rel = do
    Right names <- listDir dir | Left err => failure (dir ++ ": " ++ show err)
    if length names > 4096 then failure ("Too many entries in " ++ dir ++ " (4096)")
       else walkEntries depth dir rel (sort (filter (\n => n /= "." && n /= "..") names))

  walkEntries : Nat -> String -> String -> List String -> IO (Either String (List (String, List Bits8)))
  walkEntries depth dir rel [] = pure (Right [])
  walkEntries depth dir rel (name :: rest) = do
    let full = joinPath dir name
    let relName = if rel == "" then name else rel ++ "/" ++ name
    isDir <- isDirectoryPath full
    -- Tool and VCS directories (as in the LSP's ignore set) are not package sources;
    -- module directories are capitalized, so these lowercase names never hold modules.
    let skipped = isDir && (isPrefixOf "." name || elem name ["build", "node_modules", "__pycache__", "dist", "target"])
    Right here <- if skipped || not (isDir || isSuffixOf ".fib" name) then pure (Right (the (List (String, List Bits8)) [])) else do
          Right canonical <- exactCanonical full | Left err => failure err
          if canonical /= full then failure ("Symlink or alias in package source tree: " ++ full)
             else if isDir then walkSources depth full relName
             else do
               Right bytes <- readBytes full | Left err => failure err
               pure (Right [(relName, bytes)])
      | Left err => failure err
    Right others <- walkEntries depth dir rel rest | Left err => failure err
    if length here + length others > 2048 then failure "Package has too many source files (2048)"
       else pure (Right (here ++ others))

lockedPackage : String -> LocalRoot -> IO (Either String LockedPackage)
lockedPackage base root = do
  Right manifestBytes <- pure (bytesOf root.manifestText) | Left err => failure err
  Right files <- walkSources 16 root.sourceRoot "" | Left err => failure err
  Just tree <- pure (treeDigest files) | Nothing => failure ("Invalid source path in package " ++ root.manifest.name)
  pure (Right (MkLocked root.manifest.name (joinBy "." root.manifest.modulePrefix)
                (relativePath base root.packageRoot) (sha256Hex manifestBytes) tree))

lockedPackages : String -> List LocalRoot -> IO (Either String (List LockedPackage))
lockedPackages base [] = pure (Right [])
lockedPackages base (root :: rest) = do
  Right here <- lockedPackage base root | Left err => failure err
  Right others <- lockedPackages base rest | Left err => failure err
  pure (Right (here :: others))

||| The lock these packages would have right now.
currentLock : LocalInventory -> IO (Either String Lock)
currentLock inventory = do
  let entry = inventory.entryPackage
  Right packages <- lockedPackages entry.packageRoot inventory.packages | Left err => failure err
  pure (Right (MkLock entry.manifest.name entry.manifest.foundation packages))

lockPathFor : LocalInventory -> String
lockPathFor inventory = joinPath inventory.entryPackage.packageRoot "fibril.lock"

||| Right Nothing: no lock. Left: unreadable, not strictly decodable or non-canonical.
readLock : String -> IO (Either String (Maybe Lock))
readLock path = do
  Right file <- openFile path Read
    | Left FileNotFound => pure (Right Nothing)
    | Left err => failure (path ++ ": " ++ show err)
  closeFile file
  Right text <- loadSource path | Left err => failure (path ++ ": " ++ show err)
  pure (case decodeLock text of
    Left err => Left (path ++ ": " ++ err)
    Right lock => Right (Just lock))

||| Loads the dependency closure and, when a fibril.lock sits beside the entry
||| manifest, verifies it first so a drifted package is never half-trusted. No
||| lock means no verification. Never fetches, runs scripts or writes the lock.
public export
loadLocalInventory : String -> IO (Either String LocalInventory)
loadLocalInventory path = do
  Right inventory <- loadUnlockedInventory path | Left err => failure err
  Right recorded <- readLock (lockPathFor inventory) | Left err => failure err
  case recorded of
    Nothing => pure (Right inventory)
    Just lock => do
      Right current <- currentLock inventory | Left err => failure err
      case lockDrift lock current of
        [] => pure (Right inventory)
        drift => failure (unlines ("fibril.lock does not match the current packages (run fibril lock --update to accept):"
                                   :: map ("  " ++) drift))

||| fibril lock [--update]: write the lock beside the entry manifest. An existing
||| lock is replaced only with update, through a temporary file and rename.
||| shortcut: no fsync before the rename, so after power loss the lock may be empty
||| (then rejected as malformed and regenerated with --update).
public export
writeLock : (update : Bool) -> String -> IO (Either String (List String))
writeLock update path = do
  Right inventory <- loadUnlockedInventory path | Left err => failure err
  Right current <- currentLock inventory | Left err => failure err
  let target = lockPathFor inventory
  recorded <- readLock target
  let temporary = target ++ ".tmp"
  let write : IO (Either String ())
      write = do
        _ <- removeFile temporary -- a stale temporary from a crash is ours; never let it block locking
        Right () <- freshFile temporary (encodeLock current) | Left err => failure err
        Right () <- renamePath temporary target | Left err => do
          _ <- removeFile temporary
          failure err
        pure (Right ())
  case recorded of
    Right Nothing => do
      Right () <- write | Left err => failure err
      pure (Right ["Wrote fibril.lock (" ++ show (length current.packages) ++ " packages)"])
    _ => if not update then failure "fibril.lock already exists; use fibril lock --update to replace it" else
      case recorded of
        Right (Just old) => case lockDrift old current of
          [] => pure (Right ["fibril.lock is already up to date"])
          drift => do
            Right () <- write | Left err => failure err
            pure (Right ("Updated fibril.lock:" :: map ("  " ++) drift))
        _ => do
          Right () <- write | Left err => failure err
          pure (Right ["Replaced unreadable fibril.lock"])
