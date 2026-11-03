-- Read-only POSIX module discovery. No core checking or program execution.
module Fibril.Driver.ModuleGraph

import Data.List
import Fibril.Project.Workspace
import Fibril.Project.Local
import Fibril.Project.Manifest
import System.Directory
import Fibril.Runtime.Path
import Fibril.Source.Text
import Fibril.Source.UTF8
import Fibril.Source.Lexer
import Fibril.Source.Document
import Fibril.Source.Parser
import Fibril.Source.Declaration
import Fibril.Source.File
import Fibril.Source.Diagnostic
import Fibril.Driver.Check
import Fibril.Driver.JSON

%default total

record Site where
  constructor AtSource
  path : String
  source : String
  point : Maybe Position

public export
record GraphError where
  constructor DetailedGraphFailure
  path : String
  source : String
  point : Maybe Position
  message : String
  sourceKnown : Bool
  byteOffset : Maybe Nat
  stage : String

||| Compatibility constructor for discovery errors. Empty unknown source is not
||| represented as a purported empty-file snapshot.
public export
GraphFailure : String -> String -> Maybe Position -> String -> GraphError
GraphFailure path source point message =
  DetailedGraphFailure path source point message (source /= "") Nothing "module-graph"

failure : Site -> String -> GraphError
failure site message = GraphFailure site.path site.source site.point message

loadFailure : String -> LoadError -> GraphError
loadFailure path err = case err of
  InvalidUTF8 problem =>
    DetailedGraphFailure path "" Nothing (show err) False (Just problem.byteOffset) "decoding"
  InvalidText problem =>
    DetailedGraphFailure path "" (Just problem.position) (show err) False Nothing "source-validation"
  _ => DetailedGraphFailure path "" Nothing (show err) False Nothing "loading"

public export
renderGraphError : GraphError -> String
renderGraphError err = case (err.sourceKnown, err.point) of
  (True, Just point) => renderDiagnostic err.path err.source (AtPoint point err.message)
  _ => renderFileError err.path err.message

frontendError : String -> String -> FrontendError -> GraphError
frontendError path source err =
  let category = driverStage (FrontendFailure err)
   in case driverDiagnostic (FrontendFailure err) of
        Just diagnostic => DetailedGraphFailure path source (Just diagnostic.position)
                             diagnostic.message True Nothing category
        Nothing => DetailedGraphFailure path source Nothing (show err) True Nothing category

public export
record ModuleSnapshot where
  constructor Snapshot
  path : String
  source : String
  bytes : Nat
  document : ParsedDocument

public export
data GraphScope = SingleRoot | PackageRoots WorkspacePlan String

public export
record ModuleGraph where
  constructor ScopedGraph
  root : String
  entry : String
  modules : List ModuleSnapshot
  scope : GraphScope

||| Compatibility constructor for explicit single-root graphs.
public export
LoadedGraph : String -> String -> List ModuleSnapshot -> ModuleGraph
LoadedGraph root entry modules = ScopedGraph root entry modules SingleRoot

record Selection where
  constructor SelectedRoot
  root : String
  owner : Maybe String

selectImport : GraphScope -> Selection -> List String -> Either String Selection
selectImport SingleRoot current components = Right current
selectImport (PackageRoots plan _) current components = do
  owner <- case current.owner of Nothing => Left "Missing package owner"; Just owner => Right owner
  spec <- case moduleOwner plan owner components of Left err => Left (show err); Right spec => Right spec
  Right (SelectedRoot spec.sourceRoot (Just spec.name))

record State where
  constructor Progress
  count : Nat
  bytes : Nat
  done : List ModuleSnapshot

moduleText : List String -> String
moduleText names = concat (intersperse "." names)

byteCount : String -> Nat
byteCount source = foldl (\count, char => count +
  (if ord char <= 0x7f then 1 else if ord char <= 0x7ff then 2
   else if ord char <= 0xffff then 3 else 4)) 0 (unpack source)

modulePath : String -> String -> List String -> IO (Either String String)
modulePath root directory [] = pure (Left "Empty module name")
modulePath root directory (name :: rest) = do
  let component = case rest of [] => name ++ ".fib"; _ => name
  Right () <- exactEntry directory component
    | Left err => pure (Left err)
  let candidate = joinPath directory component
  Just canonical <- canonicalPath candidate
    | Nothing => pure (Left ("Cannot canonicalize " ++ candidate))
  if not (inside root canonical) then pure (Left "Module path escapes canonical source root")
     else case rest of
       [] => pure (Right canonical)
       _ => modulePath root canonical rest

headerMatches : Maybe (List String) -> ModuleSnapshot -> Either GraphError ()
headerMatches Nothing snapshot = Right ()
headerMatches (Just expected) snapshot = case snapshot.document.moduleHeader of
  Nothing => Left (failure (AtSource snapshot.path snapshot.source Nothing)
                   "Imported files require a module header")
  Just header => if header.components == expected then Right () else
    Left (failure (AtSource snapshot.path snapshot.source (Just header.nameSpan.start))
          ("Module header does not match requested " ++ moduleText expected))

parseSnapshot : String -> String -> Either GraphError ParsedDocument
parseSnapshot path source = case parseDocument 64 256 source of
  Left (SymbolLexical err) => Left (frontendError path source (Lexical err))
  Left (SymbolParsing err) => Left (frontendError path source (Parsing err))
  Right document => Right document

checkIdentity : String -> Maybe (List String) -> ModuleSnapshot -> IO (Either GraphError ())
checkIdentity root expected snapshot = case headerMatches expected snapshot of
  Left err => pure (Left err)
  Right () => case snapshot.document.moduleHeader of
    Nothing => pure (Right ())
    Just header => do
      let site = AtSource snapshot.path snapshot.source (Just header.nameSpan.start)
      resolved <- modulePath root root header.components
      pure $ case resolved of
        Left err => Left (failure site err)
        Right claimed => if claimed == snapshot.path then Right () else
          Left (failure site "Module/header path mismatch")

mutual
  visit : Nat -> GraphScope -> Selection -> List String -> Maybe (List String) -> Site -> String -> State ->
          IO (Either GraphError State)
  visit Z scope selected active expected site path state =
    pure (Left (failure site "Module graph depth budget exhausted"))
  visit (S depth) scope selected active expected site path state =
    case elem path active of
      True => pure (Left (failure site
        ("Import cycle: " ++ concat (intersperse " -> " (reverse (path :: active))))))
      False => case find (\snapshot => snapshot.path == path) state.done of
        Just snapshot => pure (map (const state) (headerMatches expected snapshot))
        Nothing =>
          if state.count >= 32 then pure (Left (failure site "Module count budget exceeded (32)"))
          else do
            Right source <- loadSource path
              | Left err => pure (Left (loadFailure path err))
            let bytes = byteCount source
            if state.bytes + bytes > 524288
               then pure (Left (failure site "Aggregate module source byte budget exceeded (524288)"))
               else do
                 Right document <- pure (parseSnapshot path source)
                   | Left err => pure (Left err)
                 let snapshot = Snapshot path source bytes document
                 Right () <- checkIdentity selected.root expected snapshot
                   | Left err => pure (Left err)
                 result <- imports depth scope selected (path :: active) snapshot document.imports
                            (Progress (S state.count) (state.bytes + bytes) state.done)
                 pure $ case result of
                   Left err => Left err
                   Right complete => Right ({ done := complete.done ++ [snapshot] } complete)

  imports : Nat -> GraphScope -> Selection -> List String -> ModuleSnapshot -> List ImportDeclaration -> State ->
            IO (Either GraphError State)
  imports depth scope selected active snapshot [] state = pure (Right state)
  imports depth scope selected active snapshot (dependency :: rest) state = do
    let site = AtSource snapshot.path snapshot.source (Just dependency.span.start)
    Right target <- pure (selectImport scope selected dependency.components)
      | Left err => pure (Left (failure site err))
    resolved <- modulePath target.root target.root dependency.components
    case resolved of
      Left err => pure (Left (failure site (moduleText dependency.components ++ ": " ++ err)))
      Right path => do
        result <- visit depth scope target active (Just dependency.components) site path state
        case result of
          Left err => pure (Left err)
          Right next => imports depth scope selected active snapshot rest next

||| Existing paths, canonical root containment, header matching, acyclic graph.
||| Sources are immutable in-memory snapshots, not an atomic filesystem transaction.
public export
loadModuleGraph : String -> String -> IO (Either GraphError ModuleGraph)
loadModuleGraph root entry = do
  Just rootPath <- canonicalPath root
    | Nothing => pure (Left (GraphFailure root "" Nothing "Cannot canonicalize source root"))
  Right directory <- openDir rootPath
    | Left err => pure (Left (GraphFailure rootPath "" Nothing (show err)))
  closeDir directory
  Just entryPath <- canonicalPath entry
    | Nothing => pure (Left (GraphFailure entry "" Nothing "Cannot canonicalize entry file"))
  if not (inside rootPath entryPath)
     then pure (Left (GraphFailure entryPath "" Nothing "Entry escapes canonical source root"))
     else do
       result <- visit 32 SingleRoot (SelectedRoot rootPath Nothing) [] Nothing (AtSource entryPath "" Nothing) entryPath (Progress 0 0 [])
       pure $ map (\state => LoadedGraph rootPath entryPath state.done) result

||| One traversal across canonical roots, retaining the validated package plan
||| and root owner. Each source import has both package and module permission.
||| No separately loaded graphs are concatenated; graph/source quotas are global.
public export
loadPackageModuleGraph : String -> IO (Either GraphError ModuleGraph)
loadPackageModuleGraph manifest = do
  Right inventory <- loadLocalInventory manifest
    | Left err => pure (Left (GraphFailure manifest "" Nothing err))
  let package = inventory.entryPackage
  if package.manifest.entry /= Just "Main"
     then pure (Left (GraphFailure package.manifestPath "" Nothing "Root package requires explicit entry: Main")) else do
    Right entry <- modulePath package.sourceRoot package.sourceRoot ["Main"]
      | Left err => pure (Left (GraphFailure package.manifestPath "" Nothing err))
    let scope = PackageRoots inventory.plan package.manifest.name
    result <- visit 32 scope (SelectedRoot package.sourceRoot (Just package.manifest.name)) [] (Just ["Main"])
                    (AtSource entry "" Nothing) entry (Progress 0 0 [])
    pure (map (\state => ScopedGraph package.sourceRoot entry state.done scope) result)

scopeFields : ModuleGraph -> List (String, String)
scopeFields graph = case graph.scope of
  SingleRoot => []
  PackageRoots plan entryOwner =>
    [("package_scope", jsonObject
      [("entry_package", jsonString entryOwner),
       ("inventory", jsonArray (map (\spec => jsonObject
         [("name", jsonString spec.name), ("source_root", jsonString spec.sourceRoot),
          ("module_prefix", jsonString (moduleText spec.modulePrefix)),
          ("dependencies", jsonArray (map jsonString spec.dependencies))]) plan.inventory)),
       ("module_owners", jsonArray (map (\snapshot => jsonObject
         [("path", jsonString snapshot.path), ("owner", case filter (\spec => inside spec.sourceRoot snapshot.path) plan.inventory of
           [spec] => jsonString spec.name
           _ => "null")]) graph.modules))])]

public export
renderModuleGraph : ModuleGraph -> String
renderModuleGraph graph = protocolJSON
  (scopeFields graph ++ [("checked", "false"), ("root", jsonString graph.root), ("entry", jsonString graph.entry),
   ("modules", jsonArray (map (\snapshot => jsonObject
      [("path", jsonString snapshot.path), ("bytes", show snapshot.bytes),
       ("module", maybe "null" (\header => jsonString (moduleText header.components)) snapshot.document.moduleHeader),
       ("imports", jsonArray (map (\dependency => jsonString (moduleText dependency.components)) snapshot.document.imports))]) graph.modules))])
