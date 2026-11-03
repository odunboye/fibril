-- Pure bundled scaffolding assets, independent of compiler checking and syntax.
module Fibril.Project.Template

import public Fibril.Project.Name

%default total

public export
record ProjectFile where
  constructor PlannedFile
  path : String
  contents : String

||| No hooks, fetched assets or manifest pretending to be understood by the CLI.
||| Main is fixed; the validated directory slug cannot inject code or shell text.
public export
consoleFiles : String -> List ProjectFile
consoleFiles name =
  [ PlannedFile "src/Main.fib" ("module Main\n\nmain : IO Unit\nmain = putStrLn \"Hello from " ++ name ++ "!\"\n")
  , PlannedFile ".gitignore" "build/\n"
  , PlannedFile "README.md" ("# " ++ name ++ "\n\nA minimal Fibril console project.\n\n```sh\nfibril check --source-dir src src/Main.fib\nfibril run --source-dir src src/Main.fib\n```\n\nThe compiler is an experimental bootstrap. Implicit project and workspace-member\ndiscovery are not implemented: these commands use the explicit source root.\nNo dependencies were fetched, no hooks ran, and no Git repository was initialized.\n")
  ]
