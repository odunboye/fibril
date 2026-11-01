module Main

import System
import Data.List
import Fibril.Driver.Demo
import Fibril.Source.File
import Fibril.Source.Lexer

%default total

help : String
help = """
Fibril — experimental language bootstrap

Usage:
  fibril --help
  fibril --version
  fibril demo       Run built-in ordinary checking and cubical algebra examples
  fibril validate-source PATH   Validate UTF-8 and source controls (not typing)
  fibril lex-source PATH        Print tokens/spans for the expression subset

Experimental core checkers exist. Source parsing, cubical term checking,
and C/JavaScript compilation are not implemented yet.
"""

main : IO ()
main = do
  args <- getArgs
  case drop 1 args of
    [] => putStrLn help
    ["--help"] => putStrLn help
    ["--version"] => putStrLn "Fibril 0.1.0-dev (Idris 2 bootstrap)"
    ["lex-source", path] => do
      loaded <- loadSource path
      case loaded of
        Left err => do
          putStrLn (show err)
          exitFailure
        Right source =>
          case lexSource source of
            Left err => do
              putStrLn (show err)
              exitFailure
            Right tokens => traverse_ (putStrLn . show) tokens
    ["validate-source", path] => do
      result <- loadSource path
      case result of
        Right _ => putStrLn "Source text valid (UTF-8 and control policy only; not type checked)."
        Left err => do
          putStrLn (show err)
          exitFailure
    ["demo"] =>
      case demoReport of
        Right lines => traverse_ putStrLn lines
        Left err => do
          putStrLn ("Demo failed: " ++ err)
          exitFailure
    _ => do
      putStrLn "Unsupported command. Run fibril --help."
      exitFailure
