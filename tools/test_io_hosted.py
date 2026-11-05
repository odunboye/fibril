#!/usr/bin/env python3
"""Run focused hosted IO tests without pack or project/YAML dependencies.

Requires idris2 and its Chez backend. Builds only in a temporary directory.
This is not a replacement for the full Idris, CLI or native suites.
"""
import os
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROGRAM = r'''module Main

import Data.List
import System
import Tests.IO
import Tests.ConsoleArguments
import Tests.ConsoleSequence
import Tests.ConsoleScript
import Tests.ConsoleInput
import Fibril.Effect.Console
import Fibril.Runtime.Console

main : IO ()
main = do
  hostChecks <- runSequenceChecks
  scriptHostChecks <- runScriptHostChecks
  fixture <- getEnv "FIBRIL_IO_INPUT_FIXTURE"
  inputChecks <- case fixture of
    Nothing => pure [("input fixture environment is set", False)]
    Just path => runInputFileChecks path
  let results = Tests.IO.checks ++ Tests.ConsoleArguments.checks ++
                Tests.ConsoleSequence.checks ++ Tests.ConsoleScript.checks ++
                Tests.ConsoleInput.checks ++ hostChecks ++ scriptHostChecks ++ inputChecks
  traverse_ (\(label, ok) => putStrLn ((if ok then "PASS: " else "FAIL: ") ++ label)) results
  if all snd results then pure () else exitFailure
  flushed <- executeConsoleActions [PrintLine "PASS: real stdout flush adapter"]
  case flushed of
    Left err => do putStrLn ("FAIL: " ++ err); exitFailure
    Right () => putStrLn ("HOSTED_IO_OK " ++ show (length results))
'''


INTERACTIVE = r'''module Interactive

import System
import Fibril.Effect.ConsoleProgram
import Fibril.Runtime.Console
import Fibril.Runtime.ConsoleInput

program : ConsoleProgram (Either String ())
program = Await (WriteRequest "prompt") (\written => case written of
  Left err => Finished (Left err)
  Right () => Await ReadLineRequest (\response => case response of
    Left err => Finished (Left err)
    Right Nothing => Await (WriteRequest "EOF") Finished
    Right (Just text) => Await (WriteRequest ("received:" ++ text)) Finished))

main : IO ()
main = do
  result <- runInteractiveConsoleProgram 3 32 program
  case result of
    Right (Right ()) => do
      flushed <- flushStdout
      case flushed of
        Right () => putStrLn "HOSTED_INTERACTIVE_OK"
        Left err => do putStrLn ("FAIL: " ++ err); exitFailure
    _ => do putStrLn "FAIL: interactive execution"; exitFailure
'''


def main():
    env = os.environ.copy()
    if not env.get("CHEZ"):
        chez = shutil.which("chez") or shutil.which("scheme")
        if chez:
            env["CHEZ"] = chez
    with tempfile.TemporaryDirectory(prefix="fibril-hosted-io-") as directory:
        work = Path(directory)
        (work / "Fibril").symlink_to(ROOT / "src/Fibril", target_is_directory=True)
        (work / "Tests").symlink_to(ROOT / "test/src/Tests", target_is_directory=True)
        (work / "Main.idr").write_text(PROGRAM, encoding="utf-8")
        fixture = work / "input.txt"
        fixture.write_bytes("hello\n\nλ 🌍\r\nlast\r".encode("utf-8"))
        env["FIBRIL_IO_INPUT_FIXTURE"] = str(fixture)
        result = subprocess.run(
            shlex.split(env.get("IDRIS2", "idris2")) +
            ["--source-dir", ".", "Main.idr", "--exec", "main"],
            cwd=work, env=env, capture_output=True, text=True, timeout=180,
        )
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        # Some compiler/REPL errors return zero: require the runtime sentinel.
        if result.returncode or "FAIL: " in result.stdout or not any(
            line.startswith("HOSTED_IO_OK ") for line in result.stdout.splitlines()
        ):
            raise SystemExit(1)
        (work / "Interactive.idr").write_text(INTERACTIVE, encoding="utf-8")
        for label, supplied, expected in [
            ("Unicode CRLF input", "λ 🌍\r\n", "received:λ 🌍"),
            ("EOF", "", "EOF"),
        ]:
            interactive = subprocess.run(
                shlex.split(env.get("IDRIS2", "idris2")) +
                ["--source-dir", ".", "Interactive.idr", "--exec", "main"],
                cwd=work, env=env, input=supplied, capture_output=True,
                text=True, encoding="utf-8", timeout=180,
            )
            suffix = f"prompt\n{expected}\nHOSTED_INTERACTIVE_OK\n"
            if interactive.returncode or not interactive.stdout.endswith(suffix):
                print(interactive.stdout, end="")
                print(interactive.stderr, end="", file=sys.stderr)
                raise SystemExit(f"Interactive smoke test failed: {label}")
            print(f"PASS: real interactive stdin ({label})")


if __name__ == "__main__":
    main()
