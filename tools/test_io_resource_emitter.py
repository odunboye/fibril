#!/usr/bin/env python3
"""Checked-core hosted/native scoped-resource comparisons; no source file API yet."""
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROGRAM = r'''module ResourceCompare

import Data.List
import System
import System.File
import Fibril.Core.Term
import Fibril.Driver.Native.Emit
import Fibril.Driver.Resource
import Fibril.Runtime.Console
import Fibril.Runtime.ScopedInput
import Fibril.Effect.Console
import Tests.ResourceEmission

fail : String -> IO ()
fail message = do
  _ <- fPutStrLn stderr message
  exitFailure

executeFixture : String -> String -> IO ()
executeFixture name path = case resourceFixture name path of
  Left err => fail err
  Right (term, requests) => do
    target <- getEnv "FIBRIL_RESOURCE_EMIT"
    case target of
      Just output => case emitCheckedResourceC requests 8192 term of
        Left err => fail err
        Right code => do
          written <- writeFile output code
          case written of
            Left err => fail (show err)
            Right () => putStrLn "RESOURCE_EMISSION_OK"
      Nothing => do
        result <- runResourceTermWith 128 128 requests
          (ResourceHost (\text => executeConsole (PrintLine text))
            (pure (Left "stdin unused")) flushStdout (\_, _ => pure ())) term
        case (result.outcome, result.cleanupFailures) of
          (Right (), []) => pure ()
          _ => do
            -- Explicit caller policy for observing failure prefixes, matching
            -- the C process's exit-time stdio handling. The runner itself
            -- promises final flush only on success.
            _ <- flushStdout
            case result.outcome of
              Left err => fail (show err)
              Right () => fail ("Cleanup failed: " ++ show result.cleanupFailures)

main : IO ()
main = do
  name <- getEnv "FIBRIL_RESOURCE_CASE"
  path <- getEnv "FIBRIL_RESOURCE_PATH"
  case (name, path) of
    (Just selected, Just filename) => executeFixture selected filename
    _ => fail "missing resource fixture environment"
'''

# (label, checked-core fixture, file contents, expected stdout, process status)
CASES = [
    ("Unicode CRLF read", "read", "λ 🌍\r\n".encode(), "λ 🌍\n".encode(), 0),
    ("EOF", "read", b"", b"EOF\n", 0),
    ("NUL text is rejected without truncation", "read", b"a\0b\n",
     b"File read failed: Console input contains NUL\n", 0),
    ("invalid UTF-8 lead", "read", b"\xff\n",
     b"File read failed: Console input is not valid UTF-8\n", 0),
    ("overlong UTF-8", "read", b"\xc0\x80\n",
     b"File read failed: Console input is not valid UTF-8\n", 0),
    ("UTF-8 surrogate", "read", b"\xed\xa0\x80\n",
     b"File read failed: Console input is not valid UTF-8\n", 0),
    ("UTF-8 scalar out of range", "read", b"\xf4\x90\x80\x80\n",
     b"File read failed: Console input is not valid UTF-8\n", 0),
    ("literal replacement scalar is preserved", "read", "�\n".encode(), "�\n".encode(), 0),
    ("empty line", "read", b"\n", b"\n", 0),
    ("unterminated final line", "read", b"last\r", b"last\r\n", 0),
    ("read error retains ownership", "read", b"x" * 8193 + b"\n",
     b"File read failed: Console input line length limit exceeded\n", 0),
    ("scope without read", "plain", b"hello\n", b"", 0),
    ("recursive fold inside scope", "recursive", b"hello\n", b"zero!\n", 0),
    ("runtime predecessor fold inside scope", "recursive-runtime", b"hello\n", b"zero!\n", 0),
    ("unary data fold inside scope", "recursive-unary", b"hello\n", b"end+\n", 0),
    ("sequence fold inside scope", "recursive-sequence", b"hello\n", b"headnil\n", 0),
    ("nested ownership return", "nested", b"hello\n", b"", 0),
    ("two successor reads", "twice", b"first\nsecond\n", b"first\nsecond\n", 0),
    ("read after NUL error", "twice", b"a\0b\nnext\n",
     b"File read failed: Console input contains NUL\nnext\n", 0),
    ("read after UTF-8 error", "twice", b"\xff\nnext\n",
     b"File read failed: Console input is not valid UTF-8\nnext\n", 0),
    ("byte cap drains overflowing line", "twice", b"x" * 40000 + b"\nnext\n",
     b"File read failed: Console input line length limit exceeded\nnext\n", 0),
    ("erased first pair field", "erased-first", b"", b"kept\n", 0),
    ("erased second pair field", "erased-second", b"", b"kept\n", 0),
    ("open failure category", "missing", b"", b"OPEN_FAILED\n", 0),
    ("NUL path denied", "nul", b"", b"OPEN_FAILED\n", 0),
    ("NUL output fails and closes scope", "write-nul", b"hello\n", b"", 1),
    ("request limit before acquisition", "budget-before", b"hello\n", b"", 1),
    ("request limit in owned body", "budget-body", b"hello\n", b"", 1),
    ("request limit after visible prefix", "budget-after-first", b"first\nsecond\n", b"first\n", 1),
]


def main():
    env = os.environ.copy()
    env.pop("FIBRIL_RESOURCE_EMIT", None)
    if not env.get("CHEZ"):
        chez = shutil.which("chez") or shutil.which("scheme")
        if chez:
            env["CHEZ"] = chez
    with tempfile.TemporaryDirectory(prefix="fibril-checked-resources-") as directory:
        work = Path(directory)
        (work / "Fibril").symlink_to(ROOT / "src/Fibril", target_is_directory=True)
        (work / "Tests").symlink_to(ROOT / "test/src/Tests", target_is_directory=True)
        (work / "ResourceCompare.idr").write_text(PROGRAM, encoding="utf-8")
        fixture_path = work / "file 'quoted' λ.txt"
        env["FIBRIL_RESOURCE_PATH"] = str(fixture_path)
        host_bin = work / "host-bin"
        built = subprocess.run(
            shlex.split(env.get("IDRIS2", "idris2")) + [
                "--source-dir", ".", "--output-dir", str(host_bin),
                "-o", "resource-host", "ResourceCompare.idr",
            ], cwd=work, env=env, capture_output=True, text=True, timeout=180,
        )
        host_executable = host_bin / "resource-host"
        if built.returncode or not host_executable.exists():
            raise SystemExit(built.stdout + built.stderr)
        # Run a real executable: idris2 --exec does not reliably propagate the
        # program's exitFailure status, which matters for failure comparisons.
        command = [str(host_executable)]
        compiled = {}
        for label, selected, contents, expected, status in CASES:
            fixture_path.write_bytes(contents)
            case_env = {**env, "FIBRIL_RESOURCE_CASE": selected}
            if selected not in compiled:
                source = work / f"{selected}.c"
                emitted = subprocess.run(
                    command, cwd=work, env={**case_env, "FIBRIL_RESOURCE_EMIT": str(source)},
                    capture_output=True, text=True, timeout=180,
                )
                if emitted.returncode or "RESOURCE_EMISSION_OK" not in emitted.stdout:
                    raise SystemExit(emitted.stdout + emitted.stderr)
                executable = work / selected
                subprocess.run(shlex.split(env.get("CC", "cc")) + [
                    "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(ROOT / "runtime/native"),
                    str(source), str(ROOT / "runtime/native/fibril_runtime.c"), "-o", str(executable),
                ], check=True, capture_output=True, timeout=60)
                compiled[selected] = executable
            hosted = subprocess.run(command, cwd=work, env=case_env, capture_output=True, timeout=180)
            native = subprocess.run([str(compiled[selected])], capture_output=True, timeout=10)
            for backend, result in [("hosted", hosted), ("native", native)]:
                if result.returncode != status or result.stdout != expected:
                    raise SystemExit(f"{backend} resource mismatch ({label}): {result!r}")
                if status == 0 and result.stderr:
                    raise SystemExit(f"{backend} unexpected error ({label}): {result.stderr!r}")
                failure = b"output contains NUL" if selected == "write-nul" else b"request budget"
                if status and failure not in result.stderr:
                    raise SystemExit(f"{backend} wrong failure category ({label}): {result.stderr!r}")
            print(f"PASS: checked resource hosted/native agreement ({label})")


if __name__ == "__main__":
    main()
