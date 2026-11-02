-- Version 2: project source identity must never be treated as entry-file points.
module Fibril.Driver.ProjectReport

import Fibril.Source.Text
import Fibril.Driver.JSON
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck

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

public export
projectAccepted : ProjectOutcome -> Bool
projectAccepted (ProjectAccepted _) = True
projectAccepted _ = False
