module Tests.ConsoleInput

import Data.List
import System.File
import Fibril.Runtime.ConsoleInput
import Fibril.Runtime.Console
import Fibril.Effect.ConsoleProgram

%default total

public export
checks : List (String, Bool)
checks =
  [ ("line terminator strips LF", stripLineTerminator "hello\n" == "hello")
  , ("line terminator strips CRLF", stripLineTerminator "hello\r\n" == "hello")
  , ("line terminator preserves final bare CR", stripLineTerminator "hello\r" == "hello\r")
  , ("line terminator preserves whitespace", stripLineTerminator " hello \t\n" == " hello \t")
  , ("line terminator strips only one newline", stripLineTerminator "hello\n\n" == "hello\n")
  ]

covering
rejectedLine : String -> String -> IO Bool
rejectedLine path expected = do
  opened <- openFile path Read
  case opened of
    Left _ => pure False
    Right handle => do
      first <- readConsoleLine 32 handle
      next <- readConsoleLine 32 handle
      closeFile handle
      pure (first == Left expected && next == Right (Just "next"))

||| The focused Python runner supplies an isolated fixture containing:
||| hello LF, empty LF, Unicode CRLF, then final bare-CR data without LF.
public export
covering
runInputFileChecks : String -> IO (List (String, Bool))
runInputFileChecks path = do
  opened <- openFile path Read
  case opened of
    Left err => pure [("input fixture opens: " ++ show err, False)]
    Right handle => do
      first <- readConsoleLine 32 handle
      blank <- readConsoleLine 32 handle
      unicode <- readConsoleLine 32 handle
      final <- readConsoleLine 32 handle
      eof <- readConsoleLine 32 handle
      repeatedEOF <- readConsoleLine 32 handle
      let readProgram = Await ReadLineRequest Finished
      recordedEOF <- recordConsoleProgram 1 (\_ => pure (Right ()))
                       (readConsoleLine 32 handle) readProgram
      let replayedEOF = runScript 1 recordedEOF.transcript readProgram
      closeFile handle
      reopened <- openFile path Read
      tooLong <- case reopened of
        Left _ => pure False
        Right limited => do
          result <- readConsoleLine 2 limited
          closeFile limited
          pure (result == Left "Console input line length limit exceeded")
      writeOnly <- openFile (path ++ ".write-only") WriteTruncate
      readError <- case writeOnly of
        Left _ => pure False
        Right output => do
          result <- readConsoleLine 32 output
          closeFile output
          pure $ case result of
            Left _ => True
            Right _ => False
      _ <- removeFile (path ++ ".write-only")
      nul <- rejectedLine (path ++ ".nul") "Console input contains NUL"
      invalid <- rejectedLine (path ++ ".invalid") "Console input is not valid UTF-8"
      overflow <- rejectedLine (path ++ ".overflow") "Console input line length limit exceeded"
      pure [ ("text input rejects NUL without truncation and retains next line", nul)
           , ("text input rejects invalid UTF-8 and retains next line", invalid)
           , ("text input drains an overflowing line without losing the next", overflow)
           , ("real EOF response records and replays",
                case (recordedEOF.outcome, replayedEOF.result) of
                  (Right (Right Nothing), Right (Right Nothing)) =>
                    length recordedEOF.transcript == 1 && null replayedEOF.remaining
                  _ => False)
           , ("real input read error is not EOF", readError)
           , ("real input reads a line", first == Right (Just "hello"))
           , ("real input distinguishes empty line from EOF", blank == Right (Just ""))
           , ("real input decodes Unicode and strips CRLF", unicode == Right (Just "λ 🌍"))
           , ("real input preserves unterminated final bare CR", final == Right (Just "last\r"))
           , ("real input reports EOF", eof == Right Nothing)
           , ("real input repeated EOF remains EOF", repeatedEOF == Right Nothing)
           , ("real input enforces post-read length limit", tooLong)
           ]
