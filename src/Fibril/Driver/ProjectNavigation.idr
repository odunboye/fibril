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

-- Private: the caller has already checked the entire graph, including
-- source-order visibility, privacy, and every qualified reference.
definitionIn : CheckedProject -> ModuleSnapshot -> Nat -> Nat -> Maybe SourceLocation
definitionIn project current line column =
  let graph = project.graph
      local = bindings False current
      imported : List (String, SourceLocation)
      imported = concatMap (\snapshot =>
        if snapshot.path == current.path then []
        else case snapshot.document.moduleHeader of
          Nothing => []
          Just header => if any (\dependency => dependency.components == header.components)
                                 current.document.imports
                            then bindings True snapshot else []) graph.modules
      short : String -> String
      short = \name => case reverse (forget (Data.String.split (== '.') name)) of
        [] => name
        part :: _ => part
      unqualified : String -> Maybe SourceLocation
      unqualified = \name => case filter (\entry => short (fst entry) == name) imported of
        [(_, target)] => Just target
        _ => Nothing
      references = documentReferencesWithGlobals (Located current.path) unqualified
                     (\name => lookup name (local ++ imported)) current.document
      recursionRefs = map (\site => RefersTo site.origin (Located site.path site.target))
                        (filter (\site => site.path == current.path) project.recursiveSites)
   in map target (find (\reference =>
        line == reference.origin.start.line &&
        column >= reference.origin.start.column &&
        column < reference.origin.finish.column) (recursionRefs ++ references))

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

||| Explicit entry and query paths allow querying a library without inventing
||| a main for it. No source is reparsed/reloaded for lookup after preparation.
||| Returned records are ordinary data, not navigation-correctness certificates.
public export
prepareProjectDefinition : String -> String -> Nat -> Nat -> String ->
                           IO (Either String ProjectDefinition)
prepareProjectDefinition root entry line column path = do
  checked <- checkProject root entry
  case checked of
    Left err => pure (Left (renderGraphError err))
    Right project => do
      canonical <- canonicalPath path
      pure $ case canonical >>= (\path => find (\snapshot => snapshot.path == path) project.graph.modules) of
        Nothing => Left (renderFileError path "Query file is not in the checked project graph")
        Just snapshot => Right (ProjectTarget project.graph snapshot
                                 (definitionIn project snapshot line column))

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
