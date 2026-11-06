module Tests.ConsoleScript

import Data.List
import Data.IORef
import Fibril.Runtime.Console
import Fibril.Driver.Console
import Fibril.Driver.Check
import Fibril.Core.Term
import Fibril.Effect.Console
import Fibril.Effect.ConsoleProgram

%default total

-- Explicitly distinguish a line, EOF and a represented input failure.
echo : ConsoleProgram (Either String ())
echo = Await ReadLineRequest (\response => case response of
  Left err => Finished (Left err)
  Right Nothing => Finished (Right ())
  Right (Just text) => Await (WriteRequest text) Finished)

public export
checks : List (String, Bool)
checks =
  [ ("checked source plan feeds ordered scripted requests",
      case resolveSource "main : IO Unit\nmain = do\n  putStrLn \"first\"\n  putStrLn \"second\"" of
        Left _ => False
        Right term => case prepareConsoleProgram 128 128 term of
          Left _ => False
          Right program =>
            let observed = runScript 2
                  [ExpectWrite "first" (Right ()), ExpectWrite "second" (Right ())] program in
              observed.result == Right (Right ()) &&
              length observed.transcript == 2 && null observed.remaining)
  , ("checked source program propagates scripted write failure",
      case resolveSource "main : IO Unit\nmain = do\n  putStrLn \"first\"\n  putStrLn \"second\"" of
        Left _ => False
        Right term => case prepareConsoleProgram 128 128 term of
          Left _ => False
          Right program =>
            let observed = runScript 2
                  [ExpectWrite "first" (Left "failed"), ExpectWrite "second" (Right ())] program in
              observed.result == Right (Left "failed") &&
              length observed.transcript == 1 && length observed.remaining == 1)
  , ("core program rejects wrong entry type before protocol creation",
      case prepareConsoleProgram 128 128 (IOPure (StringValue "not unit")) of
        Left _ => True
        Right _ => False)
  , ("script input response determines following write",
      let observed = runScript 2
            [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Right ())] echo in
        observed.result == Right (Right ()) && null observed.remaining &&
        length observed.transcript == 2)
  , ("script EOF produces no write",
      let observed = runScript 1 [SupplyLine (Right Nothing)] echo in
        observed.result == Right (Right ()) && length observed.transcript == 1)
  , ("script input failure is passed to the continuation",
      let observed = runScript 1 [SupplyLine (Left "input failed")] echo in
        observed.result == Right (Left "input failed") &&
        length observed.transcript == 1)
  , ("script write failure is passed to the continuation",
      let observed = runScript 2
            [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Left "write failed")] echo in
        observed.result == Right (Left "write failed") &&
        length observed.transcript == 2)
  , ("script mismatched write is not consumed",
      let observed = runScript 1 [ExpectWrite "wrong" (Right ())]
            (outputProgram [PrintLine "expected"]) in
        observed.result == Left ScriptMismatch &&
        length observed.remaining == 1 && null observed.transcript)
  , ("script rejects wrong request kind",
      let observed = runScript 1 [ExpectWrite "wrong kind" (Right ())] echo in
        observed.result == Left ScriptMismatch && length observed.remaining == 1)
  , ("script exhausted response supply is explicit",
      (runScript 1 [] echo).result == Left ScriptExhausted)
  , ("script request fuel is explicit",
      let observed = runScript 0 [SupplyLine (Right Nothing)] echo in
        observed.result == Left ScriptFuelLimit && length observed.remaining == 1)
  , ("script completed program needs no request fuel",
      (runScript 0 [] (Finished (the Nat 42))).result == Right 42)
  , ("script unused responses remain visible",
      let observed = runScript 0 [SupplyLine (Right Nothing)] (Finished ()) in
        observed.result == Right () && length observed.remaining == 1)
  , ("script adapted output stops at first write error",
      let observed = runScript 3
            [ExpectWrite "first" (Right ()), ExpectWrite "fail" (Left "failed"),
             ExpectWrite "never" (Right ())]
            (outputProgram [PrintLine "first", PrintLine "fail", PrintLine "never"]) in
        observed.result == Right (Left "failed") &&
        length observed.transcript == 2 && length observed.remaining == 1)
  , ("script preserves prefix when later request exhausts fuel",
      let observed = runScript 1
            [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Right ())] echo in
        observed.result == Left ScriptFuelLimit &&
        length observed.transcript == 1 && length observed.remaining == 1)
  ]

||| Compare the same response-dependent program against scripted and injected
||| host adapters. The event log records effects before a later failure/limit.
public export
runScriptHostChecks : IO (List (String, Bool))
runScriptHostChecks = do
  events <- newIORef (the (List String) [])
  let readLine : IO (Either String (Maybe String))
      readLine = do
        modifyIORef events ("read" ::)
        pure (Right (Just "hello"))
  let writeLine : String -> IO (Either String ())
      writeLine text = do
        modifyIORef events (("write:" ++ text) ::)
        pure (Right ())
  actual <- runConsoleProgram 2 writeLine readLine echo
  seen <- readIORef events
  let scripted = runScript 2
        [SupplyLine (Right (Just "hello")), ExpectWrite "hello" (Right ())] echo
  writeIORef events []
  limited <- runConsoleProgram 1 writeLine readLine echo
  limitedSeen <- readIORef events
  writeIORef events []
  let failWrite : String -> IO (Either String ())
      failWrite text = do
        modifyIORef events (("write:" ++ text) ::)
        pure (Left "write failed")
  failed <- runConsoleProgram 2 failWrite readLine echo
  failedSeen <- readIORef events
  unsupported <- runOutputConsoleProgram 1 echo
  recorded <- recordConsoleProgram 2 writeLine readLine echo
  recordedFailure <- recordConsoleProgram 2 failWrite readLine echo
  recordedLimit <- recordConsoleProgram 1 writeLine readLine echo
  let replay = runScript 2 recorded.transcript echo
  let failureReplay = runScript 2 recordedFailure.transcript echo
  let limitReplay = runScript 1 recordedLimit.transcript echo
  pure [ ("recorded host responses replay to the same result",
           case (recorded.outcome, replay.result) of
             (Right result, Right replayed) => result == replayed &&
               length recorded.transcript == 2 && null replay.remaining
             _ => False)
       , ("recorded operation failure replays without host effects",
           case (recordedFailure.outcome, failureReplay.result) of
             (Right (Left "write failed"), Right (Left "write failed")) =>
               length recordedFailure.transcript == 2 && null failureReplay.remaining
             _ => False)
       , ("recorded fuel exhaustion retains replayable prefix",
           case (recordedLimit.outcome, limitReplay.result) of
             (Left ConsoleRequestLimit, Left ScriptFuelLimit) =>
               length recordedLimit.transcript == 1
             _ => False)
       , ("incremental host and script agree on response-dependent output",
           case (actual, scripted.result) of
             (Right result, Right expected) => result == expected &&
               reverse seen == ["read", "write:hello"]
             _ => False)
       , ("incremental host fuel preserves earlier effects",
           case limited of
             Left ConsoleRequestLimit => reverse limitedSeen == ["read"]
             _ => False)
       , ("incremental host passes write failure to continuation",
           case failed of
             Right (Left "write failed") => reverse failedSeen == ["read", "write:hello"]
             _ => False)
       , ("incremental production adapter reports unsupported input",
           case unsupported of
             Right (Left "Console input is not implemented") => True
             _ => False)
       ]
