-- Source-aware definitions over a successfully checked immutable project graph.
module Fibril.Driver.ProjectNavigation

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Document
import Fibril.Source.Declaration
import Fibril.Source.Navigation
import Fibril.Source.Diagnostic
import Fibril.Runtime.Path
import Fibril.Project.Local
import Fibril.Project.Manifest
import Fibril.Project.Workspace
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ProjectReport
import Fibril.Driver.JSON

%default total

public export
record SourceLocation where
  constructor Located
  path : String
  range : SourceSpan

bindings : Bool -> ModuleSnapshot -> List (String, SourceLocation)
bindings onlyExports snapshot = case (snapshot.document.moduleHeader, snapshot.document.body) of
  (Just header, DeclarationDocument declarations) =>
    map (\decl => (concat (intersperse "." header.components) ++ "." ++ decl.name,
                    Located snapshot.path decl.definitionNameSpan))
      (filter (\decl => not onlyExports || decl.exported) (concatMap bindingSites declarations))
  _ => []

shortName : String -> String
shortName name = case reverse (forget (Data.String.split (== '.') name)) of
  [] => name
  part :: _ => part

unqualifiedTarget : List (String, String) -> List (String, SourceLocation) -> String -> Maybe SourceLocation
unqualifiedTarget imported origins name =
  case nub (map snd (filter (\entry => shortName (fst entry) == name) imported)) of
    [origin] => lookup origin origins
    _ => Nothing

checkedImport : List (List String, List (String, String)) -> ImportDeclaration -> List (String, String)
checkedImport exports dependency = case lookup dependency.components exports of
  Nothing => []
  Just bindings => case dependency.selectors of
    Nothing => bindings
    Just selectors => filter (\entry => elem (shortName (fst entry)) (map spelling selectors)) bindings

resolveOrigins : List (String, SourceLocation) -> List (String, String) -> List (String, SourceLocation)
resolveOrigins origins entries = mapMaybe (\(visible, origin) => map (\target => (visible, target)) (lookup origin origins)) entries

selectorTargets : Nat -> Nat -> List (String, SourceLocation) -> ImportDeclaration -> List SourceLocation
selectorTargets line column selected dependency = case dependency.selectors of
  Nothing => []
  Just selectors => mapMaybe (\selector =>
    if line == selector.span.start.line && column >= selector.span.start.column && column < selector.span.finish.column
      then lookup (concat (intersperse "." dependency.components) ++ "." ++ selector.spelling) selected
      else Nothing) selectors

-- Private: the caller has already checked the entire graph, including
-- source-order visibility, privacy, and every qualified reference.
definitionIn : ModuleGraph -> List (List String, List (String, String)) -> ModuleSnapshot -> Nat -> Nat -> Maybe SourceLocation
definitionIn graph exports current line column =
  let origins = concatMap (bindings True) graph.modules
      selected = concatMap (checkedImport exports) current.document.imports
      selectedLocations = resolveOrigins origins selected
      visible = bindings False current ++ selectedLocations
      qualifiedAliases = concatMap (\dependency => case dependency.alias of
        Nothing => []
        Just alias => map (\(name, origin) => (alias.spelling ++ "." ++ shortName name, origin))
          (checkedImport exports dependency)) current.document.imports
      aliasLocations = resolveOrigins origins qualifiedAliases
      selectorTarget = concatMap (selectorTargets line column selectedLocations) current.document.imports
      references = documentReferencesWithGlobals (Located current.path) (unqualifiedTarget selected origins)
                     (\name => lookup name (visible ++ aliasLocations)) current.document
   in case selectorTarget of
        target :: _ => Just target
        [] => map target (find (\reference =>
          line == reference.origin.start.line &&
          column >= reference.origin.start.column &&
          column < reference.origin.finish.column) references)

locationJSON : SourceLocation -> String
locationJSON location = jsonObject
  [("path", jsonString location.path),
   ("range", jsonObject [("start", jsonPosition location.range.start),
                         ("end", jsonPosition location.range.finish)])]

public export
record ProjectDefinition where
  constructor ProjectTarget
  graph : ModuleGraph
  query : ModuleSnapshot
  definition : Maybe SourceLocation
  manifest : Maybe String

locateInGraph : ModuleGraph -> List (List String, List (String, String)) -> Maybe String -> Nat -> Nat -> String -> IO (Either String ProjectDefinition)
locateInGraph graph exports manifest line column path = do
  canonical <- canonicalPath path
  pure $ case canonical >>= (\path => find (\snapshot => snapshot.path == path) graph.modules) of
    Nothing => Left (renderFileError path "Query file is not in the checked project graph")
    Just snapshot => Right (ProjectTarget graph snapshot
                             (definitionIn graph exports snapshot line column) manifest)

||| No source is reparsed/reloaded for lookup after preparation. Returned
||| records are ordinary data, not navigation-correctness certificates.
public export
prepareProjectDefinition : String -> String -> Nat -> Nat -> String ->
                           IO (Either String ProjectDefinition)
prepareProjectDefinition root entry line column path = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => locateInGraph project.graph project.checkedExports Nothing line column path

||| Package navigation checks the complete application or library inventory;
||| it neither fabricates a library main nor adds import visibility.
public export
preparePackageDefinition : String -> Nat -> Nat -> String -> IO (Either String ProjectDefinition)
preparePackageDefinition manifest line column path = do
  Just identity <- canonicalPath manifest
    | Nothing => pure (Left (renderFileError manifest "Cannot canonicalize package manifest"))
  loaded <- loadLocalPackageGraph CheckInventory manifest
  case loaded of
    Left err => pure (Left (renderGraphError err))
    Right graph => case graph.entry == "" of
      True => case checkInventoryExports graph of
        Left err => pure (Left (renderGraphError err))
        Right exports => locateInGraph graph exports (Just identity) line column path
      False => case checkModuleGraph graph of
        Left err => pure (Left (renderGraphError err))
        Right project => locateInGraph project.graph project.checkedExports (Just identity) line column path

manifestSnapshot : LocalRoot -> String
manifestSnapshot root = jsonObject
  [("name", jsonString root.manifest.name), ("path", jsonString root.manifestPath),
   ("text", jsonString root.manifestText), ("source_dir", jsonString root.manifest.sourceDirectory),
   ("dependencies", jsonArray (map (\dependency => jsonObject
     [("name", jsonString dependency.name), ("path", jsonString dependency.path)]) root.manifest.dependencies))]

manifestSnapshots : ModuleGraph -> String
manifestSnapshots graph = case graph.scope of
  SingleRoot => jsonArray []
  PackageRoots _ _ manifests => jsonArray (map manifestSnapshot manifests)

moduleResolutions : ModuleGraph -> String
moduleResolutions graph = case graph.scope of
  SingleRoot => jsonArray []
  PackageRoots plan _ _ => jsonArray (map (\snapshot => jsonObject
    [("path", jsonString snapshot.path),
     ("module", maybe "null" (\header => jsonString (concat (intersperse "." header.components))) snapshot.document.moduleHeader),
     ("source_root", case filter (\spec => inside spec.sourceRoot snapshot.path) plan.inventory of
       [spec] => jsonString spec.sourceRoot
       _ => "null")]) graph.modules)

definitionScope : ProjectDefinition -> List (String, String)
definitionScope result = case result.manifest of
  Nothing => []
  Just manifest => ("manifest", jsonString manifest) ::
    ("manifests", manifestSnapshots result.graph) ::
    ("module_resolutions", moduleResolutions result.graph) :: scopeFields result.graph

public export
renderProjectDefinition : ProjectDefinition -> String
renderProjectDefinition result = jsonObject $
  [("version", "2"), ("coordinates", jsonString "unicode-scalars;offset=0;line=1;column=1"),
   ("entry", jsonString result.graph.entry), ("root", jsonString result.graph.root),
   ("query", jsonString result.query.path), ("checked", "true"),
   ("sources", projectSourcesJSON result.graph),
   ("definition", maybe "null" locationJSON result.definition)] ++ definitionScope result

public export
projectDefinitionFile : String -> String -> Nat -> Nat -> String ->
                        IO (Either String (List String))
projectDefinitionFile root entry line column path = do
  result <- prepareProjectDefinition root entry line column path
  pure (map (\target => [renderProjectDefinition target]) result)

public export
packageDefinitionFile : String -> Nat -> Nat -> String -> IO (Either String (List String))
packageDefinitionFile manifest line column path = do
  result <- preparePackageDefinition manifest line column path
  pure (map (\target => [renderProjectDefinition target]) result)
