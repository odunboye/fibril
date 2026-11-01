module Tests.ConsoleSequence

import Data.List
import Data.IORef
import Fibril.Core.Term
import Fibril.Effect.Console
import Fibril.Driver.Check
import Fibril.Driver.Console
import Fibril.Runtime.Console

%default total

block : String
block = "main : IO Unit\nmain = do\n  putStrLn \"first\"\n  putStrLn \"second\"\n"

planned : String -> Maybe (List String)
planned source = case resolveSource source of
  Left _ => Nothing
  Right term => case prepareIO 128 128 term of
    Left _ => Nothing
    Right actions => Just (map (\(PrintLine value) => value) actions)

rejects : String -> Bool
rejects source = case checkSource False source of
  Left _ => True
  Right _ => False

commands : Nat -> String
commands Z = ""
commands (S count) = "  putStrLn \"ok\"\n" ++ commands count

public export
checks : List (String, Bool)
checks =
  [ ("IO do preserves order", planned block == Just ["first", "second"])
  , ("IO do next-line body",
      planned "main : IO Unit\nmain =\n  do\n    putStrLn \"ok\"" == Just ["ok"])
  , ("IO do comments and CRLF",
      planned "main : IO Unit\r\nmain = do\r\n  -- comment\r\n  putStrLn \"a\"\r\n\r\n  putStrLn \"b\"\r\n" == Just ["a", "b"])
  , ("IO do empty rejected", rejects "main : IO Unit\nmain = do\n")
  , ("IO do inline statement rejected", rejects "main : IO Unit\nmain = do putStrLn \"a\"")
  , ("IO do inconsistent indentation rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\"\n   putStrLn \"b\"")
  , ("IO do dedent leaves trailing input rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\"\nputStrLn \"b\"")
  , ("IO do later type failure rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\"\n  putStrLn True")
  , ("IO do action cap accepted",
      case planned ("main : IO Unit\nmain = do\n" ++ commands 64) of
        Just actions => length actions == 64
        Nothing => False)
  , ("IO do action cap rejects 65",
      rejects ("main : IO Unit\nmain = do\n" ++ commands 65))
  ]

public export
runSequenceChecks : IO (List (String, Bool))
runSequenceChecks = do
  seen <- newIORef (the (List String) [])
  let perform : ConsoleAction -> IO (Either String ())
      perform (PrintLine value) = do
        modifyIORef seen (value ::)
        pure (if value == "fail" then Left "injected output failure" else Right ())
  success <- sequenceConsole perform [PrintLine "first", PrintLine "second"]
  completed <- readIORef seen
  writeIORef seen []
  failure <- sequenceConsole perform [PrintLine "first", PrintLine "fail", PrintLine "never"]
  attempted <- readIORef seen
  pure [("console host sequencing order",
          success == Right () && reverse completed == ["first", "second"]),
        ("console host sequencing stops at failure",
          failure == Left "injected output failure" && reverse attempted == ["first", "fail"])]
