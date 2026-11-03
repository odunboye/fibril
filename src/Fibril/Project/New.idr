-- Project scaffolding orchestration, independent of the language checker.
module Fibril.Project.New

import Data.List
import System.Info
import Fibril.Project.Template
import Fibril.Runtime.Project

%default total

public export
usage : List String
usage = ["Usage: fibril new NAME [--lib] [--template console] [--module-prefix PREFIX | --source-only] [--dry-run]",
         "Creates a fresh relative directory; NAME is 1..64 lowercase ASCII letters/digits/_/-, starting with a letter.",
         "Creates fibril.yaml with explicit default namespace App. --module-prefix overrides it; --source-only omits the manifest. No overwrite, hooks, fetching, lockfile or Git initialization."]

record Options where
  constructor NewOptions
  name : String
  dryRun : Bool
  namespacePrefix : Maybe String
  library : Bool

parse : Maybe String -> Maybe String -> Maybe String -> Bool -> Bool -> Bool -> List String -> Either String Options
parse name template owned sourceOnly library dry [] = case name of
  Nothing => Left "Missing project name. Run fibril new --help."
  Just name => if not (validProjectName name) then Left "Invalid project name: use 1..64 lowercase ASCII letters/digits/_/-, starting with a letter (no paths)."
    else if not sourceOnly && not (validTestedPrefix (maybe "App" id owned)) then Left "Invalid package prefix."
    else Right (NewOptions name dry (if sourceOnly then Nothing else Just (maybe "App" id owned)) library)
parse name template owned sourceOnly True dry ("--lib" :: _) = Left "Duplicate --lib option."
parse name template owned True False dry ("--lib" :: _) = Left "--lib conflicts with --source-only."
parse name template owned False False dry ("--lib" :: rest) = parse name template owned False True dry rest
parse name template owned sourceOnly True dry ("--source-only" :: _) = Left "--source-only conflicts with --lib."
parse name template owned True library dry ("--source-only" :: _) = Left "Duplicate --source-only option."
parse name template (Just _) False library dry ("--source-only" :: _) = Left "--source-only conflicts with --module-prefix."
parse name template Nothing False library dry ("--source-only" :: rest) = parse name template Nothing True library dry rest
parse name template owned True library dry ("--module-prefix" :: _) = Left "--module-prefix conflicts with --source-only."
parse name template owned sourceOnly library True ("--dry-run" :: _) = Left "Duplicate --dry-run option."
parse name template owned sourceOnly library False ("--dry-run" :: rest) = parse name template owned sourceOnly library True rest
parse name (Just _) owned sourceOnly library dry ("--template" :: _) = Left "Duplicate --template option."
parse name Nothing owned sourceOnly library dry ("--template" :: "console" :: rest) = parse name (Just "console") owned sourceOnly library dry rest
parse name Nothing owned sourceOnly library dry ("--template" :: _) = Left "Only --template console is supported. Web/server/mobile templates are not deployable yet."
parse name template (Just _) sourceOnly library dry ("--module-prefix" :: _) = Left "Duplicate --module-prefix option."
parse name template Nothing sourceOnly library dry ("--module-prefix" :: value :: rest) =
  if validProjectPrefix value then parse name template (Just value) sourceOnly library dry rest
  else Left "Invalid module prefix: use up to 16 capitalized ASCII components within 1024 characters; Main and its descendants are reserved."
parse name template Nothing sourceOnly library dry ["--module-prefix"] = Left "Missing --module-prefix value."
parse Nothing template owned sourceOnly library dry (arg :: rest) =
  if isPrefixOf ['-', '-'] (unpack arg) then Left ("Unknown project option: " ++ arg)
  else parse (Just arg) template owned sourceOnly library dry rest
parse (Just _) template owned sourceOnly library dry (_ :: _) = Left "Unexpected project argument or option. Run fibril new --help."

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

writeDirectories : CreationOps -> String -> List String -> IO (Either String ())
writeDirectories operations name [] = pure (Right ())
writeDirectories operations name (directory :: rest) = do
  Right () <- operations.directory (name ++ "/" ++ directory) | Left err => pure (Left err)
  writeDirectories operations name rest

||| Fresh-directory creation followed by fixed exclusive files. Stop on first
||| represented failure and retain partial output: never recursively delete it.
||| This API validates names even when called without the command parser.
||| Validate optional namespace even when invoked outside the argument parser.
public export
createPackageWith : CreationOps -> String -> Maybe String -> IO (Either String ())
createPackageWith operations name namespacePrefix =
  if not (validProjectName name) then pure (Left "Invalid project name.")
  else if not (maybe True validTestedPrefix namespacePrefix) then pure (Left "Invalid module prefix.") else do
    admitted <- operations.directory name
    case admitted of
      Left error => pure (Left error)
      Right () => do
        source <- writeDirectories operations name (case namespacePrefix of Nothing => ["src"]; Just owned => ["src", "test", "test/src", "test/src/" ++ testNamespace owned])
        case source of
          Left error => pure (Left (partialReport name error))
          Right () => do
            result <- writeFiles operations name (files name namespacePrefix ++ maybe [] (\owned => testFiles name owned False) namespacePrefix)
            pure $ case result of
              Left error => Left (partialReport name error)
              Right () => Right ()

||| Independently validate the complete derived library/test namespace before IO.
public export
createLibraryWith : CreationOps -> String -> String -> IO (Either String ())
createLibraryWith operations name owned =
  if not (validProjectName name) || not (validLibraryPrefix owned) then pure (Left "Invalid library name/prefix.") else do
    Right () <- operations.directory name | Left err => pure (Left err)
    Right () <- writeDirectories operations name (libraryDirectories owned ++ ["test", "test/src", "test/src/" ++ testNamespace owned])
      | Left err => pure (Left (partialReport name err))
    result <- writeFiles operations name (libraryFiles name owned ++ testFiles name owned True)
    pure $ case result of Left err => Left (partialReport name err); Right () => Right ()

public export
createWith : CreationOps -> String -> IO (Either String ())
createWith operations name = createPackageWith operations name Nothing

nextSteps : String -> Maybe String -> List String
nextSteps name (Just namespacePrefix) = ["Created " ++ name ++ " (console package; namespace " ++ namespacePrefix ++ ").", "Next:",
  "  cd " ++ name,
  "  fibril check",
  "  fibril run",
  "  fibril test",
  "Uses fibril.yaml in the current directory only; no parent search or lockfile."]
nextSteps name Nothing = ["Created " ++ name ++ " (console template).", "Next:",
  "  cd " ++ name,
  "  fibril check --source-dir src src/Main.fib",
  "  fibril run --source-dir src src/Main.fib",
  "Use --module-prefix PREFIX to generate an explicit local package manifest; bare commands require fibril.yaml in the current directory."]

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
newProject args = case parse Nothing Nothing Nothing False False False args of
  Left error => pure (Left error)
  Right options =>
    if options.dryRun then pure (Right
      (["Dry run: would attempt fresh project " ++ options.name ++ "/"] ++
       map (\directory => "  " ++ options.name ++ "/" ++ directory ++ "/") (case options.namespacePrefix of Nothing => ["src"]; Just owned => (if options.library then libraryDirectories owned else ["src"]) ++ ["test", "test/src", "test/src/" ++ testNamespace owned]) ++
       map (\entry => "  " ++ options.name ++ "/" ++ entry.path) ((if options.library then libraryFiles options.name (maybe "App" id options.namespacePrefix) else files options.name options.namespacePrefix) ++ maybe [] (\owned => testFiles options.name owned options.library) options.namespacePrefix) ++
       ["No filesystem checks or changes performed; creation may still fail."]))
    else if not (supportedHost os)
      then pure (Left ("Project creation requires a supported POSIX bootstrap host; reported host: " ++ os))
      else do
        result <- if options.library then createLibraryWith (CreatingWith freshDirectory freshFile) options.name (maybe "App" id options.namespacePrefix)
                  else createPackageWith (CreatingWith freshDirectory freshFile) options.name options.namespacePrefix
        pure $ case result of
          Left error => Left error
          Right () => Right (if options.library then ["Created " ++ options.name ++ " (library).", "Next:", "  cd " ++ options.name, "  fibril check", "  fibril test"] else nextSteps options.name options.namespacePrefix)
