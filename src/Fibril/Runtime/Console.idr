-- Host stdout adapter; never imported by the core normalizer or checkers.
module Fibril.Runtime.Console

import System.File
import Fibril.Effect.Console

%default total

||| Execute an explicit console request. Writes can fail or partially complete;
||| validation is separate, not a sandbox/atomic-output or real-time guarantee.
public export
executeConsole : ConsoleAction -> IO (Either String ())
executeConsole (PrintLine text) = do
  result <- fPutStrLn stdout text
  pure $ case result of
    Left err => Left ("Console output failed: " ++ show err)
    Right () => Right ()

||| Sequence host actions left-to-right, stopping on the first represented error.
||| The callback boundary permits deterministic fault-injection tests; it is not
||| a source FFI, an atomic transaction, or a core normalization operation.
public export
sequenceConsole : (ConsoleAction -> IO (Either String ())) ->
                  List ConsoleAction -> IO (Either String ())
sequenceConsole perform [] = pure (Right ())
sequenceConsole perform (action :: rest) = do
  result <- perform action
  case result of
    Left err => pure (Left err)
    Right () => sequenceConsole perform rest

||| Execute a fully prepared console plan. Source validation belongs to the driver.
public export
executeConsoleActions : List ConsoleAction -> IO (Either String ())
executeConsoleActions = sequenceConsole executeConsole
