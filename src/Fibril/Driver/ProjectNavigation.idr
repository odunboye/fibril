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
definitionIn : CheckedProject -> ModuleSnapshot -> Nat -> Nat -> Maybe SourceLocation
definitionIn project current line column =
  let origins = concatMap (bindings True) project.graph.modules
      selected = concatMap (checkedImport project.checkedExports) current.document.imports
      selectedLocations = resolveOrigins origins selected
      visible = bindings False current ++ selectedLocations
      qualifiedAliases = concatMap (\dependency => case dependency.alias of
        Nothing => []
        Just alias => map (\(name, origin) => (alias.spelling ++ "." ++ shortName name, origin))
          (checkedImport project.checkedExports dependency)) current.document.imports
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

locateInProject : CheckedProject -> Nat -> Nat -> String -> IO (Either String ProjectDefinition)
locateInProject project line column path = do
  canonical <- canonicalPath path
  pure $ case canonical >>= (\path => find (\snapshot => snapshot.path == path) project.graph.modules) of
    Nothing => Left (renderFileError path "Query file is not in the checked project graph")
    Just snapshot => Right (ProjectTarget project.graph snapshot
                             (definitionIn project snapshot line column))

||| No source is reparsed/reloaded for lookup after preparation. Returned
||| records are ordinary data, not navigation-correctness certificates.
public export
prepareProjectDefinition : String -> String -> Nat -> Nat -> String ->
                           IO (Either String ProjectDefinition)
prepareProjectDefinition root entry line column path = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => locateInProject project line column path

||| Package navigation uses the same checked application dependency graph as
||| package execution; it does not add visibility or discover unrelated files.
public export
preparePackageDefinition : String -> Nat -> Nat -> String -> IO (Either String ProjectDefinition)
preparePackageDefinition manifest line column path = do
  checked <- checkPackage manifest
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => locateInProject project line column path

public export
renderProjectDefinition : ProjectDefinition -> String
renderProjectDefinition result = jsonObject
  [("version", "2"), ("coordinates", jsonString "unicode-scalars;offset=0;line=1;column=1"),
   ("entry", jsonString result.graph.entry), ("root", jsonString result.graph.root),
   ("query", jsonString result.query.path), ("checked", "true"),
   ("sources", projectSourcesJSON result.graph),
   ("definition", maybe "null" locationJSON result.definition)]

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
