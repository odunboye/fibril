-- Host-only text input. Not imported by core conversion or typing.
module Fibril.Runtime.ConsoleInput

import Data.List
import System.File
import Fibril.Source.UTF8
import Fibril.Effect.Console
import Fibril.Effect.ConsoleProgram
import Fibril.Runtime.Console

%default total

%foreign "C:fgetc,libc 6"
primReadByte : FilePtr -> PrimIO Int

||| Remove one LF terminator, optionally preceded by CR. Preserve all other
||| characters, including a final bare CR on an unterminated line.
public export
stripLineTerminator : String -> String
stripLineTerminator text = case reverse (unpack text) of
  '\n' :: '\r' :: rest => pack (reverse rest)
  '\n' :: rest => pack (reverse rest)
  _ => text

finishLine : File -> Bool -> Bool -> List Bits8 -> IO (Either String (Maybe (List Bits8)))
finishLine handle eof overflow reversed = do
  failed <- fileError handle
  pure $ if failed then Left "Console input failed"
    else if overflow then Left "Console input line length limit exceeded"
    else if eof && null reversed then Right Nothing
    else Right (Just (reverse reversed))

-- Once full, drain to LF/EOF without retaining additional bytes. This bounds
-- captured data, not blocking time or work on an arbitrarily long input line.
covering
collectLine : Nat -> File -> Bool -> List Bits8 -> IO (Either String (Maybe (List Bits8)))
collectLine available handle@(FHandle file) overflow reversed = do
  byte <- primIO (primReadByte file)
  if byte < 0 then finishLine handle True overflow reversed else
    case available of
      Z => if byte == 10 then finishLine handle False True reversed
           else collectLine Z handle True reversed
      S rest => let bytes = cast byte :: reversed in
        if byte == 10 then finishLine handle False overflow bytes
        else collectLine rest handle overflow bytes

||| Borrow a host file; never close it. Empty lines differ from EOF. Decode
||| strict UTF-8; reject NUL instead of losing data through C-string conversion.
||| Capture at most four bytes per allowed scalar plus CR/LF, then check decoded
||| length. This is a C-compatible text API, not binary IO or a blocking bound.
public export
covering
readConsoleLine : Nat -> File -> IO (Either String (Maybe String))
readConsoleLine limit handle = do
  response <- collectLine (4 * limit + 2) handle False []
  pure $ do
    bytes <- response
    case bytes of
      Nothing => Right Nothing
      Just raw => if elem 0 raw then Left "Console input contains NUL" else
        case decodeUTF8 raw of
          Left _ => Left "Console input is not valid UTF-8"
          Right text => let line = stripLineTerminator text in
            if length line <= limit then Right (Just line)
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
