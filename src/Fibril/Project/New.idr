-- Project scaffolding orchestration, independent of the language checker.
module Fibril.Project.New

import Data.List
import System.Info
import Fibril.Project.Template
import Fibril.Runtime.Project

%default total

public export
usage : List String
usage = ["Usage: fibril new NAME [--template console] [--dry-run]",
         "Creates a fresh relative directory; NAME is 1..64 lowercase ASCII letters/digits/_/-, starting with a letter.",
         "Offline console template only. No overwrite, hooks, dependencies, manifest or Git initialization."]

record Options where
  constructor NewOptions
  name : String
  dryRun : Bool

parse : Maybe String -> Maybe String -> Bool -> List String -> Either String Options
parse name template dry [] = case name of
  Nothing => Left "Missing project name. Run fibril new --help."
  Just name => if validProjectName name then Right (NewOptions name dry) else
    Left "Invalid project name: use 1..64 lowercase ASCII letters/digits/_/-, starting with a letter (no paths)."
parse name template True ("--dry-run" :: _) = Left "Duplicate --dry-run option."
parse name template False ("--dry-run" :: rest) = parse name template True rest
parse name (Just _) dry ("--template" :: _) = Left "Duplicate --template option."
parse name Nothing dry ("--template" :: "console" :: rest) = parse name (Just "console") dry rest
parse name Nothing dry ("--template" :: _) = Left "Only --template console is supported. Web/server/mobile templates are not deployable yet."
parse Nothing template dry (arg :: rest) =
  if isPrefixOf ['-', '-'] (unpack arg) then Left ("Unknown project option: " ++ arg)
  else parse (Just arg) template dry rest
parse (Just _) template dry (_ :: _) = Left "Unexpected project argument or option. Run fibril new --help."

||| Injectable effect seam for deterministic orchestration failure tests. These
||| callbacks are host operations, not proof/capability certificates.
public export
record CreationOps where
  constructor CreatingWith
  directory : String -> IO (Either String ())
  file : String -> String -> IO (Either String ())

writeFiles : CreationOps -> String -> List ProjectFile -> IO (Either String ())
writeFiles operations name [] = pure (Right ())
writeFiles operations name (entry :: rest) = do
  result <- operations.file (name ++ "/" ++ entry.path) entry.contents
  case result of
    Left error => pure (Left error)
    Right () => writeFiles operations name rest

partialReport : String -> String -> String
partialReport name error = error ++ "\nPartial project may remain at " ++ name ++ "; no rollback was attempted. Inspect it before retrying."

||| Fresh-directory creation followed by fixed exclusive files. Stop on first
||| represented failure and retain partial output: never recursively delete it.
||| This API validates names even when called without the command parser.
public export
createWith : CreationOps -> String -> IO (Either String ())
createWith operations name =
  if not (validProjectName name) then pure (Left "Invalid project name.") else do
    admitted <- operations.directory name
    case admitted of
      Left error => pure (Left error)
      Right () => do
        source <- operations.directory (name ++ "/src")
        case source of
          Left error => pure (Left (partialReport name error))
          Right () => do
            result <- writeFiles operations name (consoleFiles name)
            pure $ case result of
              Left error => Left (partialReport name error)
              Right () => Right ()

nextSteps : String -> List String
nextSteps name = ["Created " ++ name ++ " (console template).", "Next:",
  "  cd " ++ name,
  "  fibril check --source-dir src src/Main.fib",
  "  fibril run --source-dir src src/Main.fib",
  "Package manifests and implicit project discovery are not implemented yet."]

||| Runtime identifiers differ by bootstrap backend: Chez calls GNU/Linux and
||| BSD unix; RefC reports Linux/macOS. This is a POSIX selection policy, not
||| evidence that every listed host/backend has been integration-tested.
public export
supportedHost : String -> Bool
supportedHost host = elem host ["darwin", "unix", "linux", "Linux", "macOS"]

||| Parse everything before mutation. Dry-run is a pure preview: no filesystem
||| probes, permission checks, writes or promise of later admission success.
public export
newProject : List String -> IO (Either String (List String))
newProject ["--help"] = pure (Right usage)
newProject args = case parse Nothing Nothing False args of
  Left error => pure (Left error)
  Right options =>
    if options.dryRun then pure (Right
      (["Dry run: would attempt fresh console project " ++ options.name ++ "/", "  " ++ options.name ++ "/src/"] ++
       map (\entry => "  " ++ options.name ++ "/" ++ entry.path) (consoleFiles options.name) ++
       ["No filesystem checks or changes performed; creation may still fail."]))
    else if not (supportedHost os)
      then pure (Left ("Project creation requires a supported POSIX bootstrap host; reported host: " ++ os))
      else do
        result <- createWith (CreatingWith freshDirectory freshFile) options.name
        pure $ case result of
          Left error => Left error
          Right () => Right (nextSteps options.name)
