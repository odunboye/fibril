-- Host-only line input. Not imported by core conversion or typing.
module Fibril.Runtime.ConsoleInput

import System.File
import Fibril.Effect.Console
import Fibril.Effect.ConsoleProgram
import Fibril.Runtime.Console

%default total

||| Remove one LF terminator, optionally preceded by CR. Preserve all other
||| characters, including a final bare CR on an unterminated line.
public export
stripLineTerminator : String -> String
stripLineTerminator text = case reverse (unpack text) of
  '\n' :: '\r' :: rest => pack (reverse rest)
  '\n' :: rest => pack (reverse rest)
  _ => text

||| Borrow a host file; never close it. Empty lines are Just "", EOF is Nothing.
||| Length is checked after reading/decoding, not an allocation or blocking bound.
||| Decoding follows the Idris host backend; only Chez is validated here.
public export
covering
readConsoleLine : Nat -> File -> IO (Either String (Maybe String))
readConsoleLine limit handle = do
  response <- fGetLine handle
  case response of
    Left err => pure (Left ("Console input failed: " ++ show err))
    Right raw => do
      failed <- fileError handle
      if failed then pure (Left "Console input failed") else do
        eof <- fEOF handle
        if raw == "" && eof then pure (Right Nothing) else do
          let line = stripLineTerminator raw
          pure $ if length line <= limit
            then Right (Just line)
            else Left "Console input line length limit exceeded"

||| Incremental host execution with real stdin and writes. There is no implicit
||| final flush and this is not the preflighted Fibril source runner. Pending
||| stdout is flushed before each read; a flush failure prevents that read.
||| Input may block indefinitely.
public export
covering
runInteractiveConsoleProgram : Nat -> Nat -> ConsoleProgram a ->
                               IO (Either ConsoleProgramError a)
runInteractiveConsoleProgram requests lineLimit =
  runConsoleProgram requests (\text => executeConsole (PrintLine text))
                    (readAfterFlush flushStdout (readConsoleLine lineLimit stdin))
