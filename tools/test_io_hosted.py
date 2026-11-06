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
import Tests.ReadLine
import Tests.ResourceScope
import Tests.ResourceExecution
import Tests.OwnedRead
import Tests.ResourceEmission
import Tests.HandleOwnership
import Tests.ScopedOwnership
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
  resourceChecks <- runResourceChecks
  fixture <- getEnv "FIBRIL_IO_INPUT_FIXTURE"
  inputChecks <- case fixture of
    Nothing => pure [("input fixture environment is set", False)]
    Just path => do
      lines <- runInputFileChecks path
      scoped <- runScopedInputChecks path
      executed <- runResourceExecutionChecks path
      owned <- runOwnedReadChecks path
      pure (lines ++ scoped ++ executed ++ owned)
  let results = Tests.IO.checks ++ Tests.ReadLine.checks ++ Tests.HandleOwnership.checks ++ Tests.ScopedOwnership.checks ++ Tests.OwnedRead.checks ++ Tests.ResourceEmission.checks ++ Tests.ConsoleArguments.checks ++
                Tests.ConsoleSequence.checks ++ Tests.ConsoleScript.checks ++
                Tests.ConsoleInput.checks ++ hostChecks ++ scriptHostChecks ++ resourceChecks ++ inputChecks
  traverse_ (\(label, ok) => putStrLn ((if ok then "PASS: " else "FAIL: ") ++ label)) results
  if all snd results then pure () else exitFailure
  flushed <- executeConsoleActions [PrintLine "PASS: real stdout flush adapter"]
  case flushed of
    Left err => do putStrLn ("FAIL: " ++ err); exitFailure
    Right () => putStrLn ("HOSTED_IO_OK " ++ show (length results))
'''


INTERACTIVE = r'''module Interactive

import System
import Data.Fin
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Driver.Interactive
import Fibril.Effect.ConsoleProgram
import Fibril.Runtime.Console
import Fibril.Runtime.ConsoleInput

readProgram : Term 0
readProgram = IOBind readResultType UnitType ReadLine
  (Lambda Linear readResultType
    (VariantCase (Lambda Erased readResultType (IOType UnitType)) (Variable FZ)
      [WriteLine (StringValue "EOF"),
       Lambda Linear StringType (WriteLine (StringAppend (StringValue "received:") (Variable FZ))),
       Lambda Linear StringType (WriteLine (StringAppend (StringValue "error:") (Variable FZ)))]))

program : Term 0
program = IOBind UnitType UnitType (WriteLine (StringValue "prompt"))
  (Lambda Linear UnitType (UnitCase (Variable FZ) (weaken readProgram)))

main : IO ()
main = case prepareInteractive 128 128 program of
  Left err => do putStrLn ("FAIL: " ++ show err); exitFailure
  Right prepared => do
    result <- runInteractiveConsoleProgram 3 32 prepared
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
        (work / "input.txt.empty").write_bytes(b"")
        (work / "input.txt.long").write_bytes(b"x" * 8193 + b"\n")
        (work / "input.txt.nul").write_bytes(b"a\0b\nnext\n")
        (work / "input.txt.invalid").write_bytes(b"\xff\nnext\n")
        (work / "input.txt.overflow").write_bytes(b"x" * 40000 + b"\nnext\n")
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
        for module, exported_type, constructor in [
            ("ForgeScope", "ScopedInput", "InputLease"),
            ("ForgeSession", "InputSession", "Session"),
            ("ForgeOwnership", "InputOwnershipTable", "Table"),
        ]:
            (work / f"{module}.idr").write_text(
                f"module {module}\nimport Fibril.Runtime.ScopedInput\nimport Fibril.Runtime.InputOwnership\n"
                f"bad : {exported_type}\nbad = {constructor}\n", encoding="utf-8",
            )
            rejected = subprocess.run(
                shlex.split(env.get("IDRIS2", "idris2")) +
                ["--source-dir", ".", "--check", f"{module}.idr"],
                cwd=work, env=env, capture_output=True, text=True, timeout=60,
            )
            diagnostic = rejected.stdout + rejected.stderr
            if constructor not in diagnostic or not any(
                marker in diagnostic for marker in ["private", "Undefined name", "not accessible"]
            ):
                raise SystemExit("Resource constructor opacity check failed:\n" + diagnostic)
            print(f"PASS: {exported_type} constructor is inaccessible")
        (work / "Interactive.idr").write_text(INTERACTIVE, encoding="utf-8")
        for label, supplied, expected in [
            ("Unicode CRLF input", "λ 🌍\r\n", "received:λ 🌍"),
            ("EOF", "", "EOF"),
            ("NUL rejected", "a\0b\n", "error:Console input contains NUL"),
            ("literal replacement character", "�\n", "received:�"),
            ("line length failure", "x" * 33 + "\n",
             "error:Console input line length limit exceeded"),
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
            print(f"PASS: checked-core interactive stdin ({label})")


if __name__ == "__main__":
    main()
