-- Pure bundled scaffolding assets, independent of compiler checking and syntax.
module Fibril.Project.Template

%default total

public export
record ProjectFile where
  constructor PlannedFile
  path : String
  contents : String

||| A conservative directory slug, not a language/module/package identity rule.
public export
validProjectName : String -> Bool
validProjectName name = case unpack name of
  [] => False
  first :: rest => length (first :: rest) <= 64 && lower first && all allowed rest
  where
    lower : Char -> Bool
    lower c = c >= 'a' && c <= 'z'
    allowed : Char -> Bool
    allowed c = lower c || (c >= '0' && c <= '9') || c == '_' || c == '-'

||| No hooks, fetched assets or manifest pretending to be understood by the CLI.
||| Main is fixed; the validated directory slug cannot inject code or shell text.
public export
consoleFiles : String -> List ProjectFile
consoleFiles name =
  [ PlannedFile "src/Main.fib" ("module Main\n\nmain : IO Unit\nmain = putStrLn \"Hello from " ++ name ++ "!\"\n")
  , PlannedFile ".gitignore" "build/\n"
  , PlannedFile "README.md" ("# " ++ name ++ "\n\nA minimal Fibril console project.\n\n```sh\nfibril check --source-dir src src/Main.fib\nfibril run --source-dir src src/Main.fib\n```\n\nThe compiler is an experimental bootstrap. Package manifest reading and implicit\nproject discovery are not implemented: these commands use the explicit source root.\nNo dependencies were fetched, no hooks ran, and no Git repository was initialized.\n")
  ]
