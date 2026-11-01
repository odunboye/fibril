module Main

import System
import Data.List

%default total

help : String
help = """
Fibril — experimental language bootstrap

Usage:
  fibril --help
  fibril --version

The language checker and compilation backends are not implemented yet.
"""

main : IO ()
main = do
  args <- getArgs
  case drop 1 args of
    [] => putStrLn help
    ["--help"] => putStrLn help
    ["--version"] => putStrLn "Fibril 0.1.0-dev (Idris 2 bootstrap)"
    _ => do
      putStrLn "Unsupported command. Run fibril --help."
      exitFailure
