-- Project scaffolding orchestration, independent of the language checker.
module Fibril.Project.New

import Data.List
import System.Info
import Fibril.Project.Template
import Fibril.Runtime.Project

%default total

public export
usage : List String
usage = ["Usage: fibril new NAME [--template console] [--module-prefix PREFIX] [--dry-run]",
         "Creates a fresh relative directory; NAME is 1..64 lowercase ASCII letters/digits/_/-, starting with a letter.",
         "Optional --module-prefix explicitly owns a capitalized dotted namespace (not Main), and emits fibril.yaml. No overwrite, hooks, fetching, lockfile or Git initialization."]

record Options where
  constructor NewOptions
  name : String
  dryRun : Bool
  namespacePrefix : Maybe String

parse : Maybe String -> Maybe String -> Maybe String -> Bool -> List String -> Either String Options
parse name template owned dry [] = case name of
  Nothing => Left "Missing project name. Run fibril new --help."
  Just name => if validProjectName name then Right (NewOptions name dry owned) else
    Left "Invalid project name: use 1..64 lowercase ASCII letters/digits/_/-, starting with a letter (no paths)."
parse name template owned True ("--dry-run" :: _) = Left "Duplicate --dry-run option."
parse name template owned False ("--dry-run" :: rest) = parse name template owned True rest
parse name (Just _) owned dry ("--template" :: _) = Left "Duplicate --template option."
parse name Nothing owned dry ("--template" :: "console" :: rest) = parse name (Just "console") owned dry rest
parse name Nothing owned dry ("--template" :: _) = Left "Only --template console is supported. Web/server/mobile templates are not deployable yet."
parse name template (Just _) dry ("--module-prefix" :: _) = Left "Duplicate --module-prefix option."
parse name template Nothing dry ("--module-prefix" :: value :: rest) =
  if validProjectPrefix value then parse name template (Just value) dry rest
  else Left "Invalid module prefix: use up to 16 capitalized ASCII components within 1024 characters; Main and its descendants are reserved."
parse name template Nothing dry ["--module-prefix"] = Left "Missing --module-prefix value."
parse Nothing template owned dry (arg :: rest) =
  if isPrefixOf ['-', '-'] (unpack arg) then Left ("Unknown project option: " ++ arg)
  else parse (Just arg) template owned dry rest
parse (Just _) template owned dry (_ :: _) = Left "Unexpected project argument or option. Run fibril new --help."

files : String -> Maybe String -> List ProjectFile
files name Nothing = consoleFiles name
files name (Just namespacePrefix) = packageFiles name namespacePrefix

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
||| Validate optional namespace even when invoked outside the argument parser.
public export
createPackageWith : CreationOps -> String -> Maybe String -> IO (Either String ())
createPackageWith operations name namespacePrefix =
  if not (validProjectName name) then pure (Left "Invalid project name.")
  else if not (maybe True validProjectPrefix namespacePrefix) then pure (Left "Invalid module prefix.") else do
    admitted <- operations.directory name
    case admitted of
      Left error => pure (Left error)
      Right () => do
        source <- operations.directory (name ++ "/src")
        case source of
          Left error => pure (Left (partialReport name error))
          Right () => do
            result <- writeFiles operations name (files name namespacePrefix)
            pure $ case result of
              Left error => Left (partialReport name error)
              Right () => Right ()

public export
createWith : CreationOps -> String -> IO (Either String ())
createWith operations name = createPackageWith operations name Nothing

nextSteps : String -> Maybe String -> List String
nextSteps name (Just namespacePrefix) = ["Created " ++ name ++ " (console package; namespace " ++ namespacePrefix ++ ").", "Next:",
  "  cd " ++ name,
  "  fibril check --package fibril.yaml",
  "  fibril run --package fibril.yaml",
  "No lockfile or implicit project discovery is provided."]
nextSteps name Nothing = ["Created " ++ name ++ " (console template).", "Next:",
  "  cd " ++ name,
  "  fibril check --source-dir src src/Main.fib",
  "  fibril run --source-dir src src/Main.fib",
  "Use --module-prefix PREFIX to generate an explicit local package manifest; automatic discovery is not implemented."]

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
newProject args = case parse Nothing Nothing Nothing False args of
  Left error => pure (Left error)
  Right options =>
    if options.dryRun then pure (Right
      (["Dry run: would attempt fresh console project " ++ options.name ++ "/", "  " ++ options.name ++ "/src/"] ++
       map (\entry => "  " ++ options.name ++ "/" ++ entry.path) (files options.name options.namespacePrefix) ++
       ["No filesystem checks or changes performed; creation may still fail."]))
    else if not (supportedHost os)
      then pure (Left ("Project creation requires a supported POSIX bootstrap host; reported host: " ++ os))
      else do
        result <- createPackageWith (CreatingWith freshDirectory freshFile) options.name options.namespacePrefix
        pure $ case result of
          Left error => Left error
          Right () => Right (nextSteps options.name options.namespacePrefix)
