module Main

import System
import System.File
import Data.List
import Fibril.Driver.Demo
import Fibril.Driver.Check
import Fibril.Driver.CheckReport
import Fibril.Driver.Evaluate
import Fibril.Driver.Run
import Fibril.Driver.ModuleGraph
import Fibril.Driver.ModuleCheck
import Fibril.Driver.ProjectReport
import Fibril.Driver.ProjectNavigation
import Fibril.Driver.Symbols
import Fibril.Driver.Reference
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
  fibril module-graph ROOT ENTRY  Inspect local dependency graph (syntax only, POSIX)
  fibril demo       Run built-in ordinary checking and cubical algebra examples
  fibril validate-source PATH   Validate UTF-8 and source controls (not typing)
  fibril rename-preview LINE COLUMN NEWNAME PATH  Capture-checked same-file edits (no writes)
  fibril reference LINE COLUMN PATH  Built-in documentation or bundled Prelude source
  fibril references LINE COLUMN PATH  Same-file lexical occurrences, including declarations
  fibril definition --source-dir ROOT --entry ENTRY LINE COLUMN PATH  Checked project target
  fibril definition LINE COLUMN PATH  Same-file lexical target (scalar coordinates)
  fibril symbols PATH           JSON declaration ranges (syntax only, not checking)
  fibril lex-source PATH        Print source tokens/spans (not parsing/checking)
  fibril check PATH             Check a closed source program and runtime usage
  fibril check --source-dir ROOT ENTRY  Check qualified local module interfaces (POSIX)
  fibril check --json --source-dir ROOT ENTRY  Version-2 project report with source snapshots
  fibril check --json PATH      JSON runtime-check report (no effect execution)
  fibril check --erased PATH    Check only the erased ordinary fragment
  fibril run PATH              Check main : IO Unit, then execute prepared stdout requests
  fibril run --source-dir ROOT ENTRY  Check modules, then execute the complete IO plan
  fibril eval --source-dir ROOT ENTRY  Checked module reference normalization
  fibril eval --source-dir ROOT --fuel N ENTRY  Module normalization with fuel 0..4096
  fibril eval PATH              Checked reference normalization (128 reduction steps)
  fibril eval --fuel N PATH     Reference normalization with fuel 0..4096

Annotated expressions and source-ordered nonrecursive declarations are supported.
Qualified local imports require --source-dir. Recursive declarations, cubical checking,
project JSON/editor reports, and C/JS compilation are not implemented yet.
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

main : IO ()
main = do
  args <- getArgs
  case drop 1 args of
    [] => putStrLn help
    ["--help"] => putStrLn help
    ["--version"] => putStrLn "Fibril 0.1.0-dev (Idris 2 bootstrap)"
    ["module-graph", root, entry] => do
      graph <- loadModuleGraph root entry
      case graph of
        Right graph => putStrLn (renderModuleGraph graph)
        Left err => do
          _ <- fPutStrLn stderr (renderGraphError err)
          exitFailure
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
    ["definition", line, column, path] => runLocationQuery definitionFile line column path
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
