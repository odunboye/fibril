module Tests.ConsoleSequence

import Data.List
import Data.IORef
import Fibril.Core.Term
import Fibril.Effect.Console
import Fibril.Source.Console
import Fibril.Source.Lexer
import Fibril.Source.Parser
import Fibril.Source.Text
import Fibril.Driver.Check
import Fibril.Driver.Console
import Fibril.Source.Syntax
import Fibril.Driver.Evaluate
import Fibril.Runtime.Console

%default total

block : String
block = "main : IO Unit\nmain = do\n  putStrLn \"first\"\n  putStrLn \"second\"\n"

message : ConsoleAction -> String
message (PrintLine value) = value

plannedMessages : ConsoleEntry -> List String
plannedMessages entry = case prepareConsole 128 entry of
  Left _ => []
  Right actions => map message actions

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
  [ ("console do plan preserves source order",
      case prepareSource block of
        Right (ConsoleSource entry) => plannedMessages entry == ["first", "second"]
        _ => False)
  , ("console do does not enter normalization",
      case evaluateSourceDetailed 128 block of
        Left EffectfulEvaluation => True
        _ => False)
  , ("console do does not become erased proof",
      case checkSourceDetailed True block of
        Left ErasedConsole => True
        _ => False)
  , ("console do next-line body allowed",
      case prepareSource "main : IO Unit\nmain =\n  do\n    putStrLn \"ok\"" of
        Right (ConsoleSource entry) => plannedMessages entry == ["ok"]
        _ => False)
  , ("console do comments blank lines CRLF",
      case prepareSource "main : IO Unit\r\nmain = do\r\n  -- before\r\n  putStrLn \"a\"\r\n\r\n  putStrLn \"b\" -- after\r\n" of
        Right (ConsoleSource entry) => plannedMessages entry == ["a", "b"]
        _ => False)
  , ("console do empty rejected", rejects "main : IO Unit\nmain = do\n")
  , ("console do inline statement rejected",
      rejects "main : IO Unit\nmain = do putStrLn \"a\"")
  , ("console do mismatched columns rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\"\n   putStrLn \"b\"")
  , ("console do dedented action rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\"\nputStrLn \"b\"")
  , ("console do trailing tokens rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\" True")
  , ("console do unknown later primitive rejected",
      rejects "main : IO Unit\nmain = do\n  putStrLn \"a\"\n  unknown \"b\"")
  , ("console do action must fit one source line",
      rejects "main : IO Unit\nmain = do\n  putStrLn\n    \"a\"")
  , ("console do nested block rejected",
      rejects "main : IO Unit\nmain = do\n  do\n    putStrLn \"a\"")
  , ("console do action cap exact",
      case prepareSource ("main : IO Unit\nmain = do\n" ++ commands 64) of
        Right (ConsoleSource entry) => length entry.arguments == 64
        _ => False)
  , ("console do action cap exhaustion",
      rejects ("main : IO Unit\nmain = do\n" ++ commands 65))
  , ("console single literal must remain indented",
      rejects "main : IO Unit\nmain = putStrLn\n\"\"")
  , ("console do explicit zero action budget",
      case lexSource block of
        Left _ => False
        Right tokens =>
          case parseConsoleWithBudget 0 (advancePosition (At 0 1 1) (unpack block)) tokens of
            Left _ => True
            Right _ => False)
  ]

||| Fault injection exercises the production sequencer without touching stdout.
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
  writeIORef seen []
  empty <- sequenceConsole perform []
  none <- readIORef seen
  pure [("console runtime sequencer preserves action order",
          success == Right () && reverse completed == ["first", "second"]),
        ("console runtime sequencer stops at first represented failure",
          failure == Left "injected output failure" && reverse attempted == ["first", "fail"]),
        ("console runtime empty host plan performs no action",
          empty == Right () && null none)]
