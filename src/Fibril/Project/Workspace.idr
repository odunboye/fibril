-- Pure local-package planning, not manifest parsing, filesystem authority or typing.
module Fibril.Project.Workspace

import Data.List
import Fibril.Project.Name

%default total

||| Inputs supplied by a future manifest/filesystem adapter. sourceRoot is still
||| an untrusted string here: canonicalization/containment must happen before IO.
public export
record PackageSpec where
  constructor LocalPackage
  name : String
  sourceRoot : String
  modulePrefix : List String
  foundation : String
  dependencies : List String

||| Admission policy, not a limit on the language's module namespace semantics.
public export
record WorkspaceLimits where
  constructor WithinWorkspace
  packages : Nat
  edges : Nat

public export
defaultWorkspaceLimits : WorkspaceLimits
defaultWorkspaceLimits = WithinWorkspace 64 256

||| Ordinary output data, never an authorization or core-checking certificate.
public export
record WorkspacePlan where
  constructor PlannedWorkspace
  inventory : List PackageSpec
  dependencyOrder : List String

public export
record WorkspaceError where
  constructor InvalidWorkspace
  message : String

public export
Show WorkspaceError where
  show error = error.message

component : String -> Bool
component text = case unpack text of
  [] => False
  first :: rest => upper first && all allowed rest
  where
    upper : Char -> Bool
    upper c = c >= 'A' && c <= 'Z'
    allowed : Char -> Bool
    allowed c = upper c || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_'

ownsPrefix : List String -> List String -> Bool
ownsPrefix [] moduleName = True
ownsPrefix (_ :: _) [] = False
ownsPrefix (x :: xs) (y :: ys) = x == y && ownsPrefix xs ys

overlap : PackageSpec -> PackageSpec -> Bool
overlap a b = ownsPrefix a.modulePrefix b.modulePrefix || ownsPrefix b.modulePrefix a.modulePrefix

findPackage : String -> List PackageSpec -> Maybe PackageSpec
findPackage name = find (\spec => spec.name == name)

validateInventory : List PackageSpec -> List PackageSpec -> Either WorkspaceError ()
validateInventory seen [] = Right ()
validateInventory seen (spec :: rest) = do
  if not (validPackageName spec.name) then Left (InvalidWorkspace "Invalid package name") else Right ()
  if spec.sourceRoot == "" then Left (InvalidWorkspace ("Missing source root for " ++ spec.name)) else Right ()
  if null spec.modulePrefix || length spec.modulePrefix > 16 || not (all component spec.modulePrefix)
     then Left (InvalidWorkspace ("Package namespace needs nonempty ASCII capitalized identifier components: " ++ spec.name)) else Right ()
  if any (\reserved => ownsPrefix [reserved] spec.modulePrefix) ["Main"]
     then Left (InvalidWorkspace ("Reserved namespace root for " ++ spec.name)) else Right ()
  if spec.foundation /= "de-morgan" then Left (InvalidWorkspace ("Unsupported or incompatible foundation for " ++ spec.name)) else Right ()
  if any (\other => other.name == spec.name) seen then Left (InvalidWorkspace ("Duplicate package identity: " ++ spec.name)) else Right ()
  if any (\other => other.sourceRoot == spec.sourceRoot) seen then Left (InvalidWorkspace ("Duplicate declared source-root identity: " ++ show spec.sourceRoot)) else Right ()
  if any (overlap spec) seen then Left (InvalidWorkspace ("Overlapping package namespace: " ++ spec.name)) else Right ()
  validateInventory (spec :: seen) rest

validateDependencies : List PackageSpec -> PackageSpec -> List String -> List String -> Either WorkspaceError ()
validateDependencies inventory owner seen [] = Right ()
validateDependencies inventory owner seen (name :: rest) = do
  if not (validPackageName name) then Left (InvalidWorkspace ("Invalid dependency name in " ++ owner.name)) else Right ()
  if name == owner.name then Left (InvalidWorkspace ("Self dependency: " ++ owner.name)) else Right ()
  if elem name seen then Left (InvalidWorkspace ("Duplicate dependency in " ++ owner.name ++ ": " ++ name)) else Right ()
  case findPackage name inventory of
    Nothing => Left (InvalidWorkspace ("Missing dependency of " ++ owner.name ++ ": " ++ name))
    Just _ => Right ()
  validateDependencies inventory owner (name :: seen) rest

orderPackages : Nat -> List PackageSpec -> List String -> Either WorkspaceError (List String)
orderPackages fuel inventory done =
  if length done == length inventory then Right done else case fuel of
    Z => Left (InvalidWorkspace "Workspace dependency ordering budget exhausted")
    S remaining => case find (\spec => not (elem spec.name done) && all (\name => elem name done) spec.dependencies) inventory of
      Nothing => Left (InvalidWorkspace ("Dependency cycle blocks remaining packages (possibly including dependents): " ++
        show (map name (filter (\spec => not (elem spec.name done)) inventory))))
      Just spec => orderPackages remaining inventory (done ++ [spec.name])

||| Validate every declared member, not just a chosen application's reachable set.
||| Ordering is dependency-first and deterministic under inventory/dependency reorder.
||| Duplicate roots are compared as supplied; this does not detect symlink aliases.
public export
planWorkspaceWith : WorkspaceLimits -> List PackageSpec -> Either WorkspaceError WorkspacePlan
planWorkspaceWith limits inventory = do
  if null inventory then Left (InvalidWorkspace "Workspace requires at least one package") else Right ()
  if length inventory > limits.packages || foldl (\count, spec => count + length spec.dependencies) 0 inventory > limits.edges
     then Left (InvalidWorkspace "Workspace package/dependency admission budget exhausted") else Right ()
  validateInventory [] inventory
  traverse_ (\spec => validateDependencies inventory spec [] spec.dependencies) inventory
  let stable = sortBy (\a, b => compare a.name b.name) inventory
  ordered <- orderPackages (length stable) stable []
  Right (PlannedWorkspace stable ordered)

public export
planWorkspace : List PackageSpec -> Either WorkspaceError WorkspacePlan
planWorkspace = planWorkspaceWith defaultWorkspaceLimits

||| Route a module component vector to its unique owner. This checks only package
||| dependency visibility, not module syntax, file identity, exports or source safety.
||| Main entry loading is deliberately separate: no globally shared Main namespace.
public export
moduleOwner : WorkspacePlan -> String -> List String -> Either WorkspaceError PackageSpec
moduleOwner plan importer moduleName = do
  current <- case findPackage importer plan.inventory of
    Nothing => Left (InvalidWorkspace ("Unknown importing package: " ++ show importer))
    Just spec => Right spec
  if null moduleName || length moduleName > 16 || not (all component moduleName)
     then Left (InvalidWorkspace "Invalid requested module component vector") else Right ()
  owner <- case filter (\spec => not (null spec.modulePrefix) && ownsPrefix spec.modulePrefix moduleName) plan.inventory of
    [spec] => Right spec
    [] => Left (InvalidWorkspace "No package owns the requested module namespace")
    _ => Left (InvalidWorkspace "Ambiguous module namespace ownership")
  if owner.name == current.name || elem owner.name current.dependencies then Right owner
     else Left (InvalidWorkspace ("Package " ++ owner.name ++ " is not a direct dependency of " ++ current.name))
