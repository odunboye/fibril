module Main

import System
import System.File
import Data.List
import Fibril.Driver.Demo
import Fibril.Driver.Check
import Fibril.Driver.Evaluate
import Fibril.Driver.Run
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
  fibril demo       Run built-in ordinary checking and cubical algebra examples
  fibril validate-source PATH   Validate UTF-8 and source controls (not typing)
  fibril lex-source PATH        Print source tokens/spans (not parsing/checking)
  fibril check PATH             Check a closed source program and runtime usage
  fibril check --erased PATH    Check only the erased ordinary fragment
  fibril run PATH              Check main : IO Unit, then execute prepared stdout requests
  fibril eval PATH              Checked reference normalization (128 reduction steps)
  fibril eval --fuel N PATH     Reference normalization with fuel 0..4096

Annotated expressions and source-ordered nonrecursive declarations are supported.
Imports, recursive declarations, cubical checking, and C/JS compilation are not implemented yet.
"""

printReport : Either String (List String) -> IO ()
printReport (Right lines) = traverse_ putStrLn lines
printReport (Left err) = do
  putStrLn err
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

main : IO ()
main = do
  args <- getArgs
  case drop 1 args of
    [] => putStrLn help
    ["--help"] => putStrLn help
    ["--version"] => putStrLn "Fibril 0.1.0-dev (Idris 2 bootstrap)"
    ["run", path] => do
      result <- runFile path
      case result of
        Right () => pure ()
        Left err => do
          _ <- fPutStrLn stderr err
          exitFailure
    ["eval", path] => runEval 128 path
    ["eval", "--fuel", text, path] =>
      case fuelValue text of
        Just fuel => runEval fuel path
        Nothing => do
          putStrLn "Fuel must be decimal 0..4096."
          exitFailure
    ["check", path] => runCheck False path
    ["check", "--erased", path] => runCheck True path
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
