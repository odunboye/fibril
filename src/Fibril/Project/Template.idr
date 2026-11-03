-- Pure bundled scaffolding assets, independent of compiler checking and syntax.
module Fibril.Project.Template

import public Fibril.Project.Name
import Data.List
import Data.List1
import Data.String
import Fibril.Project.Workspace

%default total

||| Explicit owned namespace, never inferred from the directory slug.
public export
validProjectPrefix : String -> Bool
validProjectPrefix namespacePrefix =
  let parts = forget (split (== '.') namespacePrefix)
   in length (unpack namespacePrefix) <= 1024 && validModuleComponents parts && (case parts of "Main" :: _ => False; _ => True)

||| App and library scaffolds both generate a .Tests module.
public export
validTestedPrefix : String -> Bool
validTestedPrefix owned = validProjectPrefix owned && length (unpack owned) <= 1018 &&
  length (forget (split (== '.') owned)) < 16

||| Leave room for .Tests in the existing module/scalar admission profile.
public export
validLibraryPrefix : String -> Bool
validLibraryPrefix owned = validTestedPrefix owned

public export
libraryDirectories : String -> List String
libraryDirectories owned = directories "src" (forget (split (== '.') owned))
  where
    directories : String -> List String -> List String
    directories path [] = [path]
    directories path (component :: rest) = path :: directories (path ++ "/" ++ component) rest

public export
record ProjectFile where
  constructor PlannedFile
  path : String
  contents : String

||| Fixed source-only scaffold; package metadata is explicitly selected separately.
||| Main is fixed; the validated directory slug cannot inject code or shell text.
public export
consoleFiles : String -> List ProjectFile
consoleFiles name =
  [ PlannedFile "src/Main.fib" ("module Main\n\nmain : IO Unit\nmain = putStrLn \"Hello from " ++ name ++ "!\"\n")
  , PlannedFile ".gitignore" "build/\n"
  , PlannedFile "README.md" ("# " ++ name ++ "\n\nA minimal Fibril console project.\n\n```sh\nfibril check --source-dir src src/Main.fib\nfibril run --source-dir src src/Main.fib\n```\n\nThe compiler is an experimental bootstrap. This source-only project uses the explicit source-root commands above.\nBare commands require ./fibril.yaml; workspace-member discovery is not implemented.\nNo dependencies were fetched, no hooks ran, and no Git repository was initialized.\n")
  ]

||| Caller validates name/namespacePrefix before effects; interpolation is restricted to
||| their ASCII profiles. This pure plan is not an acceptance certificate.
public export
packageFiles : String -> String -> List ProjectFile
packageFiles name namespacePrefix =
  filter (\file => file.path /= "README.md") (consoleFiles name) ++
  [ PlannedFile ("src/" ++ concat (intersperse "/" (forget (split (== '.') namespacePrefix))) ++ "/Tests.fib")
      ("module " ++ namespacePrefix ++ ".Tests\n\n-- Starter smoke suite: replace True with application assertions.\n-- This does not execute or assert the application IO.\nmain : Bool\nmain = True\n")
  , PlannedFile "fibril.yaml" ("schema: 1\nname: \"" ++ name ++ "\"\nmodule-prefix: \"" ++ namespacePrefix ++ "\"\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ntests: \"" ++ namespacePrefix ++ ".Tests\"\ndependencies: {}\n")
  , PlannedFile "README.md" ("# " ++ name ++ "\n\nA local Fibril console package owning " ++ namespacePrefix ++ ".\n\n```sh\nfibril check\nfibril run\nfibril test\n```\n\nMain is the separate application entry; the library namespace is explicit.\nThe generated Bool smoke suite starts with True: replace it with application\nassertions. It does not execute or verify application IO.\nNo lockfile, dependencies, hooks or Git repository were created/fetched.\nBare commands use only ./fibril.yaml; no parent search. Workspace-member files\nand locked builds are not implemented.\n")
  ]

||| Fixed library plus a real pure Bool test entry, with no application Main.
public export
libraryFiles : String -> String -> List ProjectFile
libraryFiles name owned =
  let stem = concat (intersperse "/" (forget (split (== '.') owned)))
   in [ PlannedFile ("src/" ++ stem ++ ".fib")
          ("module " ++ owned ++ "\n\nexport\nidentity : (1 value : Bool) -> Bool\nidentity = \\(1 value : Bool) => value\n")
      , PlannedFile ("src/" ++ stem ++ "/Tests.fib")
          ("module " ++ owned ++ ".Tests\nimport " ++ owned ++ "\n\nmain : Bool\nmain = " ++ owned ++ ".identity True\n")
      , PlannedFile ".gitignore" "build/\n"
      , PlannedFile "fibril.yaml"
          ("schema: 1\nname: \"" ++ name ++ "\"\nmodule-prefix: \"" ++ owned ++ "\"\nsource-dir: src\nfoundation: de-morgan\nmodules: [\"" ++ owned ++ "\"]\ntests: \"" ++ owned ++ ".Tests\"\ndependencies: {}\n")
      , PlannedFile "README.md"
          ("# " ++ name ++ "\n\nA Fibril library owning " ++ owned ++ ".\n\n```sh\nfibril check\nfibril test\n```\n\nThe test entry returns Bool: True passes, False fails. Evaluation is bounded.\nNo application Main, network, hooks, dependencies, locks or Git initialization.\n") ]
