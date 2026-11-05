-- Host-side request/response protocol. Not source syntax or a core IO runner.
module Fibril.Effect.ConsoleProgram

import Fibril.Effect.Console

%default total

||| EOF is Right Nothing; a represented input error is Left message.
public export
data ConsoleRequest : Type -> Type where
  WriteRequest : String -> ConsoleRequest (Either String ())
  ReadLineRequest : ConsoleRequest (Either String (Maybe String))

||| Host descriptions only: callbacks may depend on an interpreter's response.
||| Fuel is required by interpreters; this is not a termination certificate.
public export
data ConsoleProgram : Type -> Type where
  Finished : a -> ConsoleProgram a
  Await : ConsoleRequest response -> (response -> ConsoleProgram a) -> ConsoleProgram a

||| Adapt an already prepared output plan without adding source-level effects.
||| Stop on the first represented write failure, as the existing adapter does.
public export
outputProgram : List ConsoleAction -> ConsoleProgram (Either String ())
outputProgram [] = Finished (Right ())
outputProgram (PrintLine text :: rest) =
  Await (WriteRequest text) (\response => case response of
    Left err => Finished (Left err)
    Right () => outputProgram rest)

||| A strict script validates outgoing text as well as supplying responses.
public export
data ConsoleScriptStep
  = ExpectWrite String (Either String ())
  | SupplyLine (Either String (Maybe String))

public export
data ScriptError = ScriptExhausted | ScriptMismatch | ScriptFuelLimit

public export
Eq ScriptError where
  ScriptExhausted == ScriptExhausted = True
  ScriptMismatch == ScriptMismatch = True
  ScriptFuelLimit == ScriptFuelLimit = True
  _ == _ = False

public export
record ScriptResult a where
  constructor Scripted
  result : Either ScriptError a
  remaining : List ConsoleScriptStep
  ||| Matched requests with their scripted responses, in execution order.
  transcript : List ConsoleScriptStep

-- Record a matched request even if its scripted response represents failure.
prepend : ConsoleScriptStep -> ScriptResult a -> ScriptResult a
prepend step (Scripted result remaining transcript) =
  Scripted result remaining (step :: transcript)

||| A pure, bounded host interpreter. Fuel counts requests, not Finished nodes.
||| Unmatched/unhandled requests are not consumed; unused script is returned.
||| Represented operation errors are passed to callbacks, not thrown by the runner.
public export
runScript : Nat -> List ConsoleScriptStep -> ConsoleProgram a -> ScriptResult a
runScript fuel script (Finished value) = Scripted (Right value) script []
runScript Z script (Await request next) = Scripted (Left ScriptFuelLimit) script []
runScript (S fuel) [] (Await request next) = Scripted (Left ScriptExhausted) [] []
runScript (S fuel) script@(step :: rest) (Await (WriteRequest text) next) =
  case step of
    ExpectWrite expected response =>
      if text == expected
         then prepend step (runScript fuel rest (next response))
         else Scripted (Left ScriptMismatch) script []
    SupplyLine _ => Scripted (Left ScriptMismatch) script []
runScript (S fuel) script@(step :: rest) (Await ReadLineRequest next) =
  case step of
    SupplyLine response => prepend step (runScript fuel rest (next response))
    ExpectWrite _ _ => Scripted (Left ScriptMismatch) script []
