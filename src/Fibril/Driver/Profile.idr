||| Per-phase wall-clock timing for single-file `check`. Developer tooling: it runs
||| the same public phases as `checkSourceDetailed` one at a time and times each.
||| Idris is strict, so each phase finishes before the next clock read.
module Fibril.Driver.Profile

import Data.String
import System.Clock
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Driver.Check
import Fibril.Driver.Limits
import Fibril.Driver.Prelude
import Fibril.Source.Diagnostic
import Fibril.Source.File
import Fibril.Source.Global

%default total

public export
record Profiled where
  constructor MkProfiled
  result : Either String (List String)
  phases : List (String, Integer) -- completed phases in order, nanoseconds

now : IO Integer
now = do
  clock <- clockTime Monotonic
  pure (toNano clock)

pad3 : Integer -> String
pad3 n = let s = show n in replicate (minus 3 (length s)) '0' ++ s

||| Milliseconds with three decimals, integer arithmetic only.
export
millis : Integer -> String
millis ns = show (ns `div` 1000000) ++ "." ++ pad3 ((ns `mod` 1000000) `div` 1000)

export
renderProfile : List (String, Integer) -> String
renderProfile phases = unlines
  ("profile (monotonic wall clock, one run, not averaged):"
    :: map (\(name, ns) => "  " ++ padRight 14 ' ' name ++ millis ns ++ " ms") phases
    ++ ["  " ++ padRight 14 ' ' "total" ++ millis (sum (map snd phases)) ++ " ms"])

||| shortcut: single file, ordinary runtime checking only; no --erased, --json or
||| project modes. Upgrade by threading the same clock through ModuleCheck.
export
profileCheck : String -> IO Profiled
profileCheck path = do
  t0 <- now
  loaded <- loadSource path
  t1 <- now
  let load = ("load", t1 - t0)
  case loaded of
    Left err => pure (MkProfiled (Left (renderFileError path (show err))) [load])
    Right source => case preludeGlobals of
      Left err => do
        t2 <- now
        pure (MkProfiled (Left (renderDriverError path source (FrontendFailure (PreludeUnavailable err))))
                         [load, ("prelude", t2 - t1)])
      Right _ => do
        t2 <- now
        let prelude = ("prelude", t2 - t1)
        case prepareSource source of
          Left err => do
            t3 <- now
            pure (MkProfiled (Left (renderDriverError path source (FrontendFailure err)))
                             [load, prelude, ("frontend", t3 - t2)])
          Right (CoreSource term reports) => do
            t3 <- now
            let frontend = ("frontend", t3 - t2)
            case inferRuntime checkingDepth typeReductionFuel Empty term of
              Left err => do
                t4 <- now
                pure (MkProfiled (Left (renderDriverError path source (RuntimeFailure err)))
                                 [load, prelude, frontend, ("runtime-check", t4 - t3)])
              Right checked => do
                lines <- pure (reports ++ ["Runtime checking: accepted", "Type: " ++ renderType checked.inferredType])
                t4 <- now
                pure (MkProfiled (Right lines) [load, prelude, frontend, ("runtime-check", t4 - t3)])
