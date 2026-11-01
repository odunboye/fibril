module Main

import System
import Data.List
import Fibril.Driver.Demo

%default total

help : String
help = """
Fibril — experimental language bootstrap

Usage:
  fibril --help
  fibril --version
  fibril demo       Run built-in ordinary checking and cubical algebra examples

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
    ["demo"] =>
      case demoReport of
        Right lines => traverse_ putStrLn lines
        Left err => do
          putStrLn ("Demo failed: " ++ err)
          exitFailure
    _ => do
      putStrLn "Unsupported command. Run fibril --help."
      exitFailure
