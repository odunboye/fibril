module Main

import System
import Fibril.Project.New
import System.File
import Data.List
import Fibril.Driver.Demo
import Fibril.Driver.Check
import Fibril.Driver.CheckReport
import Fibril.Driver.Evaluate
import Fibril.Driver.Run
import Fibril.Driver.Binary
import Fibril.Driver.Interactive.Run
-- Keep the experimental resource library in the application package's build
-- closure so installed test dependencies include it; no CLI command exposes it.
import Fibril.Driver.Resource
-- Internal byte transport is built/installed, not exposed as a source primitive.
import Fibril.Runtime.Binary
import Fibril.Driver.Native
import Fibril.Driver.Test
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ProjectReport
import Fibril.Driver.ProjectNavigation
import Fibril.Driver.Symbols
import Fibril.Driver.Reference
import Fibril.Driver.Elaborate
import Fibril.Driver.Manifest
import Fibril.Driver.Format
import Fibril.Source.File
import Fibril.Source.Lexer
import Fibril.Source.Diagnostic

%default total

help : String
help = """
Fibril — experimental language bootstrap

Usage:
  fibril --help
  fibril --version
  fibril new NAME [--lib] [--template console] [--module-prefix PREFIX | --source-only] [--dry-run]  Create a fresh offline console project (POSIX)
  fibril manifest PATH          Inspect a strict local YAML manifest (no dependency/source loading)
  fibril module-graph ROOT ENTRY  Inspect local dependency graph (syntax only, POSIX)
  fibril module-graph --package PATH  Inspect package-scoped source graph (syntax only)
  fibril demo       Run built-in ordinary checking and cubical algebra examples
  fibril validate-source PATH   Validate UTF-8 and source controls (not typing)
  fibril rename-preview LINE COLUMN NEWNAME PATH  Capture-checked same-file edits (no writes)
  fibril format PATH            Format spacing and guarded expression layout to stdout (no writes)
  fibril format --json PATH     Version-1 original/formatted snapshot report
  fibril format --check PATH    Reject noncanonical spacing without output
  fibril elaborate PATH         Inspect expanded named IR (unchecked; no effects)
  fibril reference LINE COLUMN PATH  Built-in documentation or bundled Prelude source
  fibril references LINE COLUMN PATH  Same-file lexical occurrences, including declarations
  fibril definition --source-dir ROOT --entry ENTRY LINE COLUMN PATH  Checked project target
  fibril definition --package MANIFEST LINE COLUMN PATH  Checked application or library package target
  fibril definition LINE COLUMN PATH  Same-file lexical target (scalar coordinates)
  fibril symbols PATH           JSON declaration ranges (syntax only, not checking)
  fibril lex-source PATH        Print source tokens/spans (not parsing/checking)
  fibril check PATH             Check a closed source program and runtime usage
  fibril check --source-dir ROOT ENTRY  Check qualified local module interfaces (POSIX)
  fibril check                 Check app entry or library inventory in ./fibril.yaml
  fibril test                  Check all listed modules, evaluate tests main : Bool
  fibril test --package PATH   Same pure test workflow for an explicit package
  fibril emit-c PATH           Check and emit experimental C source to stdout
  fibril emit-c-binary PATH      Emit explicit binary-only C (standalone)
  fibril emit-c-interactive PATH  Emit incremental C with stdin support (standalone)
  fibril emit-c --source-dir ROOT ENTRY  Check modules and emit C
  fibril emit-c --package PATH  Check a local package and emit C
  fibril run                   Check ./fibril.yaml, then execute its IO plan
  fibril module-graph          Inspect ./fibril.yaml source graph (syntax only)
  fibril check --package PATH   Check explicit local fibril.yaml dependency closure (POSIX)
  fibril run --package PATH     Check local packages, then execute the complete IO plan
  fibril check --json --source-dir ROOT ENTRY  Version-2 project report with source snapshots
  fibril check --json PATH      JSON runtime-check report (no effect execution)
  fibril check --erased PATH    Check only the erased ordinary fragment
  fibril run PATH              Check main : IO Unit, then execute prepared stdout requests
  fibril run-binary PATH       Execute checked borrowed binary stdio (standalone)
  fibril run-interactive PATH  Execute incremental stdin/stdout IO (standalone)
  fibril run --source-dir ROOT ENTRY  Check modules, then execute the complete IO plan
  fibril eval --source-dir ROOT ENTRY  Checked module reference normalization
  fibril eval --source-dir ROOT --fuel N ENTRY  Module normalization with fuel 0..4096
  fibril eval PATH              Checked reference normalization (128 reduction steps)
  fibril eval --fuel N PATH     Reference normalization with fuel 0..4096

Annotated expressions and source-ordered nonrecursive declarations are supported.
Qualified imports use --source-dir or explicit --package. Manifest inspection
alone does not load dependencies. Workspace-member discovery and locks are absent. Recursive declarations, cubical checking, and C/JS
compilation beyond the experimental C subset are not implemented yet.
"""

printReport : Either String (List String) -> IO ()
printReport (Right lines) = traverse_ putStrLn lines
printReport (Left err) = do
  putStrLn err
  exitFailure

printServiceReport : Either String (List String) -> IO ()
printServiceReport (Right lines) = traverse_ putStrLn lines
printServiceReport (Left err) = do
  _ <- fPutStrLn stderr err
  exitFailure

printExecution : Either String () -> IO ()
printExecution (Right ()) = pure ()
printExecution (Left err) = do
  _ <- fPutStrLn stderr err
  exitFailure

printC : Either String String -> IO ()
printC (Right source) = putStr source
printC (Left err) = do
  _ <- fPutStrLn stderr err
  exitFailure

runCheck : Bool -> String -> IO ()
runCheck erasedOnly path = checkFile erasedOnly path >>= printReport

runEval : Nat -> String -> IO ()
runEval fuel path = evaluateFile fuel path >>= printReport

fuelValue : String -> Maybe Nat
fuelValue text =
  let chars = unpack text
   in if not (null chars) && length chars <= 4 && all (\c => c >= '0' && c <= '9') chars
         then let value : Nat = foldl (\n, c => n * 10 + cast (ord c - ord '0')) 0 chars
               in if value <= 4096 then Just value else Nothing
         else Nothing

coordinate : String -> Maybe Nat
coordinate text =
  let chars = unpack text
   in if not (null chars) && length chars <= 6 && all (\c => c >= '0' && c <= '9') chars
         then let value : Nat = foldl (\n, c => n * 10 + cast (ord c - ord '0')) 0 chars
               in if value > 0 && value <= 65537 then Just value else Nothing
         else Nothing

runLocationQuery : (Nat -> Nat -> String -> IO (Either String (List String))) ->
                   String -> String -> String -> IO ()
runLocationQuery query line column path = do
  result <- case (coordinate line, coordinate column) of
    (Just line, Just column) => query line column path
    _ => pure (Left "Coordinates must be decimal 1..65537 (Unicode scalars).")
  case result of
    Right lines => traverse_ putStrLn lines
    Left err => do
      _ <- fPutStrLn stderr err
      exitFailure

packageCheck : String -> IO ()
packageCheck manifest = do
  checked <- checkLocalPackage manifest
  printServiceReport (case checked of Left err => Left (renderGraphError err); Right report => Right report)

packageGraph : String -> IO ()
packageGraph manifest = do
  loaded <- loadLocalPackageGraph CheckInventory manifest
  printServiceReport (case loaded of Left err => Left (renderGraphError err); Right graph => Right [renderModuleGraph graph])

covering
main : IO ()
main = do
  args <- getArgs
  case drop 1 args of
    [] => putStrLn help
    ["--help"] => putStrLn help
    ["--version"] => putStrLn "Fibril 0.1.0-dev (Idris 2 bootstrap)"
    "new" :: options => newProject options >>= printServiceReport
    ["manifest", path] => manifestFile path >>= printServiceReport
    ["check"] => packageCheck "fibril.yaml"
    ["test"] => testPackage "fibril.yaml" >>= printServiceReport
    ["test", "--package", manifest] => testPackage manifest >>= printServiceReport
    ["run"] => runPackage "fibril.yaml" >>= printExecution
    ["emit-c"] => emitCPackage "fibril.yaml" >>= printC
    ["emit-c", "--package", manifest] => emitCPackage manifest >>= printC
    ["emit-c", "--source-dir", root, entry] => emitCProject root entry >>= printC
    ["emit-c", path] => emitCFile path >>= printC
    ["emit-c-binary", path] => emitBinaryCFile path >>= printC
    ["emit-c-interactive", path] => emitInteractiveCFile path >>= printC
    ["run-binary", path] => runBinaryFile path >>= printExecution
    ["run-interactive", path] => runInteractiveFile path >>= printExecution
    ["module-graph"] => packageGraph "fibril.yaml"
    ["module-graph", "--package", manifest] => packageGraph manifest
    ["module-graph", root, entry] => do
      graph <- loadModuleGraph root entry
      case graph of
        Right graph => putStrLn (renderModuleGraph graph)
        Left err => do
          _ <- fPutStrLn stderr (renderGraphError err)
          exitFailure
    ["run", "--package", manifest] => runPackage manifest >>= printExecution
    ["check", "--package", manifest] => packageCheck manifest
    ["run", "--source-dir", root, entry] => runProject root entry >>= printExecution
    ["run", path] => runFile path >>= printExecution
    ["eval", "--source-dir", root, entry] => evaluateProjectFile 128 root entry >>= printServiceReport
    ["eval", "--source-dir", root, "--fuel", text, entry] =>
      case fuelValue text of
        Just fuel => evaluateProjectFile fuel root entry >>= printServiceReport
        Nothing => printServiceReport (Left "Fuel must be decimal 0..4096.")
    ["eval", path] => runEval 128 path
    ["eval", "--fuel", text, path] =>
      case fuelValue text of
        Just fuel => runEval fuel path
        Nothing => do
          putStrLn "Fuel must be decimal 0..4096."
          exitFailure
    ["rename-preview", line, column, name, path] => runLocationQuery (\row, col, file => renameFile row col name file) line column path
    ["definition", "--source-dir", root, "--entry", entry, line, column, path] =>
      runLocationQuery (projectDefinitionFile root entry) line column path
    ["definition", "--package", manifest, line, column, path] =>
      runLocationQuery (packageDefinitionFile manifest) line column path
    ["definition", line, column, path] => runLocationQuery definitionFile line column path
    ["format", path] => do
      result <- formatFile False path
      case result of
        Right text => putStr text
        Left err => printServiceReport (Left err)
    ["format", "--json", path] => formatFileReport path >>= printServiceReport
    ["format", "--check", path] => do
      result <- formatFile True path
      case result of
        Right _ => pure ()
        Left err => printServiceReport (Left err)
    ["elaborate", path] => elaborateFile path >>= printServiceReport
    ["reference", line, column, path] => runLocationQuery referenceFile line column path
    ["references", line, column, path] => runLocationQuery referencesFile line column path
    ["symbols", path] => do
      result <- symbolsFile path
      case result of
        Right lines => traverse_ putStrLn lines
        Left err => do
          _ <- fPutStrLn stderr err
          exitFailure
    ["check", "--json", "--source-dir", root, entry] => do
      outcome <- prepareProject root entry
      putStrLn (renderProjectReport entry outcome)
      if projectAccepted outcome then pure () else exitFailure
    ["check", "--source-dir", root, entry] => do
      result <- checkProject root entry
      case result of
        Right project => traverse_ putStrLn (projectReport project)
        Left err => do
          _ <- fPutStrLn stderr (renderGraphError err)
          exitFailure
    ["check", path] => runCheck False path
    ["check", "--erased", path] => runCheck True path
    ["check", "--json", path] => do
      report <- checkFileReport path
      putStrLn (renderCheckReport report)
      if isAccepted report then pure () else exitFailure
    ["lex-source", path] => do
      loaded <- loadSource path
      case loaded of
        Left err => do
          putStrLn (renderFileError path (show err))
          exitFailure
        Right source =>
          case lexSource source of
            Left err => do
              putStrLn (renderDriverError path source (FrontendFailure (Lexical err)))
              exitFailure
            Right tokens => traverse_ (putStrLn . show) tokens
    ["validate-source", path] => do
      result <- loadSource path
      case result of
        Right _ => putStrLn "Source text valid (UTF-8 and control policy only; not type checked)."
        Left err => do
          putStrLn (renderFileError path (show err))
          exitFailure
    ["demo"] => printReport demoReport
    _ => do
      putStrLn "Unsupported command. Run fibril --help."
      exitFailure
