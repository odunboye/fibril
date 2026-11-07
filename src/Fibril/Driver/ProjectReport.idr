-- Version 2: project source identity must never be treated as entry-file points.
module Fibril.Driver.ProjectReport

import Fibril.Source.Text
import Fibril.Driver.JSON
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck
import Fibril.Project.Local

%default total

sourceJSON : String -> String -> String
sourceJSON path source = jsonObject [("path", jsonString path), ("text", jsonString source)]

sourcesJSON : ModuleGraph -> List String
sourcesJSON graph = map (\snapshot => sourceJSON snapshot.path snapshot.source) graph.modules

public export
projectSourcesJSON : ModuleGraph -> String
projectSourcesJSON graph = jsonArray (sourcesJSON graph)

diagnosticJSON : GraphError -> String
diagnosticJSON err = jsonObject
  [("path", jsonString err.path), ("severity", jsonString "error"),
   ("stage", jsonString err.stage), ("message", jsonString err.message),
   ("position", maybe "null" jsonPosition err.point),
   ("byteOffset", maybe "null" show err.byteOffset),
   ("sourceAvailable", if err.sourceKnown then "true" else "false")]

reportJSON : String -> Maybe String -> Bool -> List String -> List String -> List String -> String
reportJSON entry root accepted report sources diagnostics = jsonObject
  [("version", "2"),
   ("coordinates", jsonString "unicode-scalars;offset=0;line=1;column=1"),
   ("entry", jsonString entry), ("root", maybe "null" jsonString root),
   ("accepted", if accepted then "true" else "false"),
   ("report", jsonArray (map jsonString report)),
   ("sources", jsonArray sources), ("diagnostics", jsonArray diagnostics)]

||| Contains original project source text. A source snapshot is data, not a proof
||| that a current filesystem/editor buffer still matches it.
public export
renderProjectReport : String -> ProjectOutcome -> String
renderProjectReport requestedEntry (GraphUnavailable err) =
  reportJSON requestedEntry Nothing False []
    (if err.sourceKnown then [sourceJSON err.path err.source] else [])
    [diagnosticJSON err]
renderProjectReport requestedEntry (ProjectRejected graph err) =
  reportJSON graph.entry (Just graph.root) False [] (sourcesJSON graph) [diagnosticJSON err]
renderProjectReport requestedEntry (ProjectAccepted project) =
  reportJSON project.graph.entry (Just project.graph.root) True (projectReport project)
    (sourcesJSON project.graph) []

||| Structured package diagnostics for applications and entry-free libraries.
||| Inventory checking does not invent an application entry or execute effects.
public export
packageCheckReport : String -> IO (Bool, String)
packageCheckReport manifest = do
  loaded <- loadLocalPackageGraph CheckInventory manifest
  pure $ case loaded of
    Left err => (False, renderProjectReport manifest (GraphUnavailable err))
    Right graph => if graph.entry == "" then
      case checkInventoryGraph graph of
        Left err => (False, renderProjectReport manifest (ProjectRejected graph err))
        Right () => (True, reportJSON graph.entry (Just graph.root) True
          ["Library checking: accepted (no runtime entry)"] (sourcesJSON graph) [])
      else case checkModuleGraph graph of
        Left err => (False, renderProjectReport manifest (ProjectRejected graph err))
        Right project => (True, renderProjectReport manifest (ProjectAccepted project))

public export
projectAccepted : ProjectOutcome -> Bool
projectAccepted (ProjectAccepted _) = True
projectAccepted _ = False
