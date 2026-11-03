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
  , PlannedFile "README.md" ("# " ++ name ++ "\n\nA minimal Fibril console project.\n\n```sh\nfibril check --source-dir src src/Main.fib\nfibril run --source-dir src src/Main.fib\n```\n\nThe compiler is an experimental bootstrap. Implicit project and workspace-member\ndiscovery are not implemented: these commands use the explicit source root.\nNo dependencies were fetched, no hooks ran, and no Git repository was initialized.\n")
  ]

||| Caller validates name/namespacePrefix before effects; interpolation is restricted to
||| their ASCII profiles. This pure plan is not an acceptance certificate.
public export
packageFiles : String -> String -> List ProjectFile
packageFiles name namespacePrefix =
  filter (\file => file.path /= "README.md") (consoleFiles name) ++
  [ PlannedFile "fibril.yaml" ("schema: 1\nname: \"" ++ name ++ "\"\nmodule-prefix: \"" ++ namespacePrefix ++ "\"\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies: {}\n")
  , PlannedFile "README.md" ("# " ++ name ++ "\n\nA local Fibril console package owning " ++ namespacePrefix ++ ".\n\n```sh\nfibril check --package fibril.yaml\nfibril run --package fibril.yaml\n```\n\nMain is the separate application entry; the library namespace is explicit.\nNo lockfile, dependencies, hooks or Git repository were created/fetched.\nImplicit discovery, workspace-member files and locked builds are not implemented.\n")
  ]
