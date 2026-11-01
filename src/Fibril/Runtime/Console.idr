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
