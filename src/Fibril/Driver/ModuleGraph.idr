-- Read-only POSIX module discovery. No core checking or program execution.
module Fibril.Driver.ModuleGraph

import Data.List
import System.Directory
import Fibril.Runtime.Path
import Fibril.Source.Text
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
  constructor GraphFailure
  path : String
  source : String
  point : Maybe Position
  message : String

failure : Site -> String -> GraphError
failure site message = GraphFailure site.path site.source site.point message

public export
renderGraphError : GraphError -> String
renderGraphError err = case err.point of
  Nothing => renderFileError err.path err.message
  Just point => renderDiagnostic err.path err.source (AtPoint point err.message)

frontendError : String -> String -> FrontendError -> GraphError
frontendError path source err = case driverDiagnostic (FrontendFailure err) of
  Just diagnostic => GraphFailure path source (Just diagnostic.position) diagnostic.message
  Nothing => GraphFailure path source Nothing (show err)

public export
record ModuleSnapshot where
  constructor Snapshot
  path : String
  source : String
  bytes : Nat
  document : ParsedDocument

public export
record ModuleGraph where
  constructor LoadedGraph
  root : String
  entry : String
  modules : List ModuleSnapshot

record State where
  constructor Progress
  count : Nat
  bytes : Nat
  done : List ModuleSnapshot

joinPath : String -> String -> String
joinPath root name = root ++ (if root == "/" then "" else "/") ++ name

inside : String -> String -> Bool
inside root path = root == path || isPrefixOf (unpack (joinPath root "")) (unpack path)

moduleText : List String -> String
moduleText names = concat (intersperse "." names)

byteCount : String -> Nat
byteCount source = foldl (\count, char => count +
  (if ord char <= 0x7f then 1 else if ord char <= 0x7ff then 2
   else if ord char <= 0xffff then 3 else 4)) 0 (unpack source)

-- Bound entries examined per lookup; stop once exact spelling is established.
-- Oversized directories can exhaust this search budget depending on OS ordering.
scanDirectory : Nat -> Directory -> String -> IO (Either String Bool)
scanDirectory budget directory wanted = do
  result <- nextDirEntry directory
  case result of
    Left err => pure (Left (show err))
    Right Nothing => pure (Right False)
    Right (Just name) => case budget of
      Z => pure (Left "Directory lookup entry budget exceeded (4096)")
      S rest => if name == wanted then pure (Right True) else scanDirectory rest directory wanted

exactEntry : String -> String -> IO (Either String ())
exactEntry directory wanted = do
  Right handle <- openDir directory
    | Left err => pure (Left (show err))
  result <- scanDirectory 4096 handle wanted
  closeDir handle
  pure $ case result of
    Left err => Left ("Cannot perform exact-case lookup: " ++ err)
    Right False => Left ("Missing exact-case path component " ++ show wanted)
    Right True => Right ()

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
  visit : Nat -> String -> List String -> Maybe (List String) -> Site -> String -> State ->
          IO (Either GraphError State)
  visit Z root active expected site path state =
    pure (Left (failure site "Module graph depth budget exhausted"))
  visit (S depth) root active expected site path state =
    case elem path active of
      True => pure (Left (failure site
        ("Import cycle: " ++ concat (intersperse " -> " (reverse (path :: active))))))
      False => case find (\snapshot => snapshot.path == path) state.done of
        Just snapshot => pure (map (const state) (headerMatches expected snapshot))
        Nothing =>
          if state.count >= 32 then pure (Left (failure site "Module count budget exceeded (32)"))
          else do
            Right source <- loadSource path
              | Left err => pure (Left (failure (AtSource path "" Nothing) (show err)))
            let bytes = byteCount source
            if state.bytes + bytes > 524288
               then pure (Left (failure site "Aggregate module source byte budget exceeded (524288)"))
               else do
                 Right document <- pure (parseSnapshot path source)
                   | Left err => pure (Left err)
                 let snapshot = Snapshot path source bytes document
                 Right () <- checkIdentity root expected snapshot
                   | Left err => pure (Left err)
                 result <- imports depth root (path :: active) snapshot document.imports
                            (Progress (S state.count) (state.bytes + bytes) state.done)
                 pure $ case result of
                   Left err => Left err
                   Right complete => Right ({ done := complete.done ++ [snapshot] } complete)

  imports : Nat -> String -> List String -> ModuleSnapshot -> List ImportDeclaration -> State ->
            IO (Either GraphError State)
  imports depth root active snapshot [] state = pure (Right state)
  imports depth root active snapshot (dependency :: rest) state = do
    let site = AtSource snapshot.path snapshot.source (Just dependency.span.start)
    resolved <- modulePath root root dependency.components
    case resolved of
      Left err => pure (Left (failure site (moduleText dependency.components ++ ": " ++ err)))
      Right path => do
        result <- visit depth root active (Just dependency.components) site path state
        case result of
          Left err => pure (Left err)
          Right next => imports depth root active snapshot rest next

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
       result <- visit 32 rootPath [] Nothing (AtSource entryPath "" Nothing) entryPath (Progress 0 0 [])
       pure $ map (\state => LoadedGraph rootPath entryPath state.done) result

public export
renderModuleGraph : ModuleGraph -> String
renderModuleGraph graph = protocolJSON
  [("checked", "false"), ("root", jsonString graph.root), ("entry", jsonString graph.entry),
   ("modules", jsonArray (map (\snapshot => jsonObject
      [("path", jsonString snapshot.path), ("bytes", show snapshot.bytes),
       ("module", maybe "null" (\header => jsonString (moduleText header.components)) snapshot.document.moduleHeader),
       ("imports", jsonArray (map (\dependency => jsonString (moduleText dependency.components)) snapshot.document.imports))]) graph.modules))]
