module Tests.ConsoleSequence

import Data.List
import Data.Fin
import Fibril.Core.Quantity
import Fibril.Driver.Limits
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

-- Construct core descriptions directly so the parser's do-block limit cannot
-- mask the planner's independent, global write allowance.
writePrefix : Nat -> Term 0 -> Term 0
writePrefix Z tail = tail
writePrefix (S count) tail =
  IOBind UnitType UnitType (WriteLine (StringValue "ok"))
    (Lambda Linear UnitType
      (UnitCase (Variable FZ) (weaken (writePrefix count tail))))

writeChain : Nat -> Term 0
writeChain count = writePrefix count (IOPure UnitValue)

expensiveText : Nat -> Term 0
expensiveText Z = StringValue "end"
expensiveText (S count) = StringAppend (StringValue "") (expensiveText count)

public export
checks : List (String, Bool)
checks =
  [ ("IO core plan accepts exactly the write allowance",
      case prepareIO 128 128 (writeChain consoleActionLimit) of
        Right actions => length actions == consoleActionLimit
        Left _ => False)
  , ("IO core plan rejects writes beyond the allowance",
      case prepareIO 128 128 (writeChain (S consoleActionLimit)) of
        Left PlanActionLimit => True
        _ => False)
  , ("IO expensive write requires more reduction fuel",
      case prepareIO 128 128 (WriteLine (expensiveText 129)) of
        Left PlanReductionLimit => True
        _ => False)
  , ("IO exhausted action allowance rejects before text normalization",
      case prepareIO 128 128
             (writePrefix consoleActionLimit (WriteLine (expensiveText 129))) of
        Left PlanActionLimit => True
        _ => False)
  , ("IO do preserves order", planned block == Just ["first", "second"])
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
  writeIORef seen []
  let flush : IO (Either String ())
      flush = do
        modifyIORef seen ("flush" ::)
        pure (Right ())
  flushed <- sequenceConsoleWithFlush perform flush [PrintLine "first", PrintLine "second"]
  flushedEvents <- readIORef seen
  writeIORef seen []
  failedWrite <- sequenceConsoleWithFlush perform flush [PrintLine "fail", PrintLine "never"]
  failedEvents <- readIORef seen
  writeIORef seen []
  empty <- sequenceConsoleWithFlush perform flush []
  emptyEvents <- readIORef seen
  writeIORef seen []
  let failFlush : IO (Either String ())
      failFlush = do
        modifyIORef seen ("flush failed" ::)
        pure (Left "injected flush failure")
  failedFlush <- sequenceConsoleWithFlush perform failFlush [PrintLine "first"]
  flushFailureEvents <- readIORef seen
  writeIORef seen []
  let read : IO (Either String (Maybe String))
      read = do
        modifyIORef seen ("read" ::)
        pure (Right (Just "response"))
  readResult <- readAfterFlush flush read
  readEvents <- readIORef seen
  writeIORef seen []
  blockedRead <- readAfterFlush failFlush read
  blockedEvents <- readIORef seen
  writeIORef seen []
  let failedRead : IO (Either String (Maybe String))
      failedRead = do
        modifyIORef seen ("read failed" ::)
        pure (Left "injected input failure")
  readFailure <- readAfterFlush flush failedRead
  readFailureEvents <- readIORef seen
  nulOutput <- executeConsole (PrintLine "a\0b")
  pure [("console rejects NUL output instead of truncating it",
          nulOutput == Left "Console output contains NUL"),
        ("console prompt flush precedes input",
          readResult == Right (Just "response") && reverse readEvents == ["flush", "read"]),
        ("console prompt flush failure prevents input",
          blockedRead == Left "injected flush failure" && reverse blockedEvents == ["flush failed"]),
        ("console input failure survives successful prompt flush",
          readFailure == Left "injected input failure" &&
          reverse readFailureEvents == ["flush", "read failed"]),
        ("console flush follows all successful writes",
          flushed == Right () && reverse flushedEvents == ["first", "second", "flush"]),
        ("console write failure skips final flush",
          failedWrite == Left "injected output failure" && reverse failedEvents == ["fail"]),
        ("console empty plan still flushes",
          empty == Right () && reverse emptyEvents == ["flush"]),
        ("console flush failure is returned after writes",
          failedFlush == Left "injected flush failure" &&
          reverse flushFailureEvents == ["first", "flush failed"]),
        ("console host sequencing order",
          success == Right () && reverse completed == ["first", "second"]),
        ("console host sequencing stops at failure",
          failure == Left "injected output failure" && reverse attempted == ["first", "fail"])]
