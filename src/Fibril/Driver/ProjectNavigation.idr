-- Source-aware definitions over a successfully checked immutable project graph.
module Fibril.Driver.ProjectNavigation

import Data.List
import Data.List1
import Data.Maybe
import Data.String
import Fibril.Core.Quantity
import Fibril.Source.Text
import Fibril.Source.Lexer
import Fibril.Source.Document
import Fibril.Source.Declaration
import Fibril.Source.Syntax
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

public export
record NavigationOccurrence where
  constructor Occurs
  origin : SourceLocation
  destination : SourceLocation
  isDeclaration : Bool

sameSpan : SourceSpan -> SourceSpan -> Bool
sameSpan left right = left.start.offset == right.start.offset && left.finish.offset == right.finish.offset

sameLocation : SourceLocation -> SourceLocation -> Bool
sameLocation left right = left.path == right.path && sameSpan left.range right.range

contains : Nat -> Nat -> SourceSpan -> Bool
contains line column span =
  (line > span.start.line || (line == span.start.line && column >= span.start.column)) &&
  (line < span.finish.line || (line == span.finish.line && column < span.finish.column))

moduleLocation : ModuleGraph -> List String -> Maybe SourceLocation
moduleLocation graph names = case mapMaybe (\snapshot => case snapshot.document.moduleHeader of
    Just header => if header.components == names then Just (Located snapshot.path header.nameSpan) else Nothing
    Nothing => Nothing) graph.modules of
  [target] => Just target
  _ => Nothing

-- Resolve only the current module or a checked direct import/alias, never a
-- same-spelled module elsewhere on disk. Re-exported symbols retain their own
-- defining declaration identity, while the qualifier names the facade module.
qualifierTarget : ModuleGraph -> ModuleSnapshot -> String -> Maybe SourceLocation
qualifierTarget graph current name =
  let qualifier = reverse (drop 1 (reverse (forget (Data.String.split (== '.') name))))
      own = the (List (List String)) $ case current.document.moduleHeader of
        Just header => if header.components == qualifier then [qualifier] else []
        Nothing => []
      imports = map components (filter (\dependency => dependency.components == qualifier ||
        maybe False (\alias => qualifier == [alias.spelling]) dependency.alias) current.document.imports)
   in case nub (own ++ imports) of
        [names] => moduleLocation graph names
        _ => Nothing

importReferences : ModuleGraph -> List (String, SourceLocation) -> ImportDeclaration -> List (ReferenceTo SourceLocation)
importReferences graph selected dependency =
  (case moduleLocation graph dependency.components of
    Nothing => []
    Just target => RefersTo dependency.nameSpan target ::
      maybe [] (\alias => [RefersTo alias.span target]) dependency.alias) ++
  (case dependency.selectors of
    Nothing => []
    Just selectors => mapMaybe (\selector => map (RefersTo selector.span)
      (lookup (concat (intersperse "." dependency.components) ++ "." ++ selector.spelling) selected)) selectors)

isDeclarationSite : ModuleSnapshot -> ReferenceTo SourceLocation -> Bool
isDeclarationSite current reference =
  sameLocation (Located current.path reference.origin) reference.target ||
  (reference.target.path == current.path && case current.document.body of
    DeclarationDocument declarations => any (\site => sameSpan site.nameSpan reference.origin &&
      sameSpan site.definitionNameSpan reference.target.range) (concatMap bindingSites declarations)
    _ => False)

-- These source facts are consumed only after graph checking has succeeded.
-- The generic walker handles lexical scopes; checked exports canonicalize
-- aliases/re-exports, and checker-produced sites override recursive self calls.
referencesIn : ModuleGraph -> List (String, SourceLocation) -> List (List String, List (String, String)) ->
               List RecursiveSite -> ModuleSnapshot -> List NavigationOccurrence
referencesIn graph origins exports sites current =
  let selected = concatMap (checkedImport exports) current.document.imports
      selectedLocations = resolveOrigins origins selected
      visible = bindings False current ++ selectedLocations
      qualifiedAliases = concatMap (\dependency => case dependency.alias of
        Nothing => []
        Just alias => map (\(name, origin) => (alias.spelling ++ "." ++ shortName name, origin))
          (checkedImport exports dependency)) current.document.imports
      aliasLocations = resolveOrigins origins qualifiedAliases
      references = documentReferencesWithModules (Located current.path) (unqualifiedTarget selected origins)
                     (\name => lookup name (visible ++ aliasLocations)) (qualifierTarget graph current) current.document
      recursionRefs = map (\site => RefersTo site.origin (Located site.path site.target))
                        (filter (\site => site.path == current.path) sites)
      headerRefs = maybe [] (\header => [RefersTo header.nameSpan (Located current.path header.nameSpan)]) current.document.moduleHeader
      ordinaryRefs = headerRefs ++ concatMap (importReferences graph selectedLocations) current.document.imports ++ references
      allRefs = recursionRefs ++ filter (\reference => not (any (\recursive => sameSpan reference.origin recursive.origin) recursionRefs)) ordinaryRefs
   in map (\reference => Occurs (Located current.path reference.origin) reference.target (isDeclarationSite current reference)) allRefs

originOrder : NavigationOccurrence -> NavigationOccurrence -> Ordering
originOrder left right = case compare left.origin.path right.origin.path of
  EQ => compare (left.origin.range.start.offset, left.origin.range.finish.offset)
                (right.origin.range.start.offset, right.origin.range.finish.offset)
  order => order

uniqueOccurrences : Maybe SourceLocation -> List NavigationOccurrence -> List NavigationOccurrence
uniqueOccurrences previous [] = []
uniqueOccurrences previous (reference :: rest) =
  if maybe False (sameLocation reference.origin) previous then uniqueOccurrences previous rest
  else reference :: uniqueOccurrences (Just reference.origin) rest

navigationIndex : ModuleGraph -> List (List String, List (String, String)) -> List RecursiveSite -> List NavigationOccurrence
navigationIndex graph exports sites =
  let origins = concatMap (bindings True) graph.modules
   in uniqueOccurrences Nothing (sortBy originOrder
        (concatMap (referencesIn graph origins exports sites) graph.modules))

selectedAt : List NavigationOccurrence -> String -> Nat -> Nat -> Maybe NavigationOccurrence
selectedAt index path line column = find (\reference => reference.origin.path == path &&
  contains line column reference.origin.range) index

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
  origin : Maybe SourceLocation
  referenceIndex : List NavigationOccurrence

locateInGraph : ModuleGraph -> List (List String, List (String, String)) -> List RecursiveSite -> Maybe String -> Nat -> Nat -> String -> IO (Either String ProjectDefinition)
locateInGraph graph exports sites manifest line column path = do
  canonical <- canonicalPath path
  pure $ case canonical >>= (\path => find (\snapshot => snapshot.path == path) graph.modules) of
    Nothing => Left (renderFileError path "Query file is not in the checked project graph")
    Just snapshot =>
      let index = navigationIndex graph exports sites
          selected = selectedAt index snapshot.path line column
       in Right (ProjectTarget graph snapshot (map destination selected) manifest (map origin selected) index)

||| No source is reparsed/reloaded for lookup after preparation. Returned
||| records are ordinary data, not navigation-correctness certificates.
public export
prepareProjectDefinition : String -> String -> Nat -> Nat -> String ->
                           IO (Either String ProjectDefinition)
prepareProjectDefinition root entry line column path = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => locateInGraph project.graph project.checkedExports project.recursiveSites Nothing line column path

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
      True => case checkInventoryNavigation graph of
        Left err => pure (Left (renderGraphError err))
        Right (exports, sites) => locateInGraph graph exports sites (Just identity) line column path
      False => case checkModuleGraph graph of
        Left err => pure (Left (renderGraphError err))
        Right project => locateInGraph project.graph project.checkedExports project.recursiveSites (Just identity) line column path

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

navigationReport : ProjectDefinition -> List (String, String) -> String
navigationReport result fields = jsonObject $
  [("version", "2"), ("coordinates", jsonString "unicode-scalars;offset=0;line=1;column=1"),
   ("entry", jsonString result.graph.entry), ("root", jsonString result.graph.root),
   ("query", jsonString result.query.path), ("checked", "true"),
   ("sources", projectSourcesJSON result.graph)] ++ fields ++ definitionScope result

public export
renderProjectDefinition : ProjectDefinition -> String
renderProjectDefinition result = navigationReport result
  [("definition", maybe "null" locationJSON result.definition),
   ("origin", maybe "null" locationJSON result.origin)]

occurrenceOrder : NavigationOccurrence -> NavigationOccurrence -> Ordering
occurrenceOrder left right = case compare left.origin.path right.origin.path of
  EQ => compare left.origin.range.start.offset right.origin.range.start.offset
  order => order

occurrenceJSON : NavigationOccurrence -> String
occurrenceJSON reference = jsonObject
  [("path", jsonString reference.origin.path),
   ("range", jsonObject [("start", jsonPosition reference.origin.range.start),
                          ("end", jsonPosition reference.origin.range.finish)]),
   ("declaration", if reference.isDeclaration then "true" else "false")]

public export
renderProjectReferences : ProjectDefinition -> String
renderProjectReferences result =
  let occurrences = case result.definition of
        Nothing => []
        Just selected => sortBy occurrenceOrder (filter (\reference => sameLocation reference.destination selected) result.referenceIndex)
   in navigationReport result
        [("definition", maybe "null" locationJSON result.definition),
         ("references", jsonArray (map occurrenceJSON occurrences))]

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

||| All occurrences of one canonical declaration/module in the checked closure.
||| Declaration flags let clients apply includeDeclaration without guessing.
public export
projectReferencesFile : String -> String -> Nat -> Nat -> String -> IO (Either String (List String))
projectReferencesFile root entry line column path = do
  result <- prepareProjectDefinition root entry line column path
  pure (map (\target => [renderProjectReferences target]) result)

public export
packageReferencesFile : String -> Nat -> Nat -> String -> IO (Either String (List String))
packageReferencesFile manifest line column path = do
  result <- preparePackageDefinition manifest line column path
  pure (map (\target => [renderProjectReferences target]) result)
