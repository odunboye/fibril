#!/usr/bin/env python3
"""Compare standalone source interactive drivers on Chez and emitted native C.

Exercises source input and file drivers without project/YAML loading.
"""
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROGRAM = r'''module InteractiveCompare

import System
import System.File
import Fibril.Driver.Interactive.Run

fail : String -> IO ()
fail message = do
  _ <- fPutStrLn stderr message
  exitFailure

main : IO ()
main = do
  sourcePath <- getEnv "FIBRIL_INTERACTIVE_SOURCE"
  case sourcePath of
    Nothing => fail "missing source fixture"
    Just path => do
      target <- getEnv "FIBRIL_INTERACTIVE_EMIT"
      case target of
        Just output => do
          emitted <- emitInteractiveCFile path
          case emitted of
            Left err => fail err
            Right code => do
              saved <- writeFile output code
              case saved of
                Left err => fail (show err)
                Right () => putStrLn "INTERACTIVE_EMISSION_OK"
        Nothing => do
          result <- runInteractiveFile path
          case result of
            Left err => fail err
            Right () => pure ()
'''


def main():
    env = os.environ.copy()
    env.pop("FIBRIL_INTERACTIVE_EMIT", None)
    if not env.get("CHEZ"):
        chez = shutil.which("chez") or shutil.which("scheme")
        if chez:
            env["CHEZ"] = chez
    with tempfile.TemporaryDirectory(prefix="fibril-interactive-compare-") as directory:
        work = Path(directory)
        (work / "Fibril").symlink_to(ROOT / "src/Fibril", target_is_directory=True)
        (work / "Tests").symlink_to(ROOT / "test/src/Tests", target_is_directory=True)
        (work / "InteractiveCompare.idr").write_text(PROGRAM, encoding="utf-8")
        shutil.copyfile(ROOT / "examples/core/read-line.fib", work / "read-line.fib")
        env["FIBRIL_INTERACTIVE_SOURCE"] = str(work / "read-line.fib")
        command = shlex.split(env.get("IDRIS2", "idris2")) + [
            "--source-dir", ".", "InteractiveCompare.idr", "--exec", "main",
        ]
        emitted = subprocess.run(
            command, cwd=work, env={**env, "FIBRIL_INTERACTIVE_EMIT": str(work / "io.c")},
            capture_output=True, text=True, timeout=180,
        )
        if emitted.returncode or "INTERACTIVE_EMISSION_OK" not in emitted.stdout:
            raise SystemExit(emitted.stdout + emitted.stderr)
        executable = work / "io"
        subprocess.run(
            shlex.split(env.get("CC", "cc")) + [
                "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(ROOT / "runtime/native"),
                str(work / "io.c"), str(ROOT / "runtime/native/fibril_runtime.c"), "-o", str(executable),
            ], check=True, capture_output=True, timeout=60,
        )
        cases = [
            ("Unicode CRLF", "λ 🌍\r\n", "received:λ 🌍"),
            ("EOF", "", "EOF"),
            ("NUL input rejected", "a\0b\n", "error:Console input contains NUL"),
            ("invalid UTF-8 rejected", b"\xff\n", "error:Console input is not valid UTF-8"),
            ("literal replacement scalar", "�\n", "received:�"),
            ("empty line", "\n", "received:"),
            ("unterminated line", "hello", "received:hello"),
            ("bare final CR", "hello\r", "received:hello\r"),
            ("length error", "x" * 8193 + "\n", "error:Console input line length limit exceeded"),
            ("Unicode length boundary", "🌍" * 8192 + "\n", "received:" + "🌍" * 8192),
        ]
        for label, supplied, reply in cases:
            encoded = supplied if isinstance(supplied, bytes) else supplied.encode("utf-8")
            hosted = subprocess.run(
                command, cwd=work, env=env, input=encoded, capture_output=True, timeout=180,
            )
            native = subprocess.run([str(executable)], input=encoded, capture_output=True, timeout=10)
            expected = ("prompt\n" + reply + "\n").encode("utf-8")
            for backend, result in [("hosted", hosted), ("native", native)]:
                if result.returncode or result.stdout != expected or result.stderr:
                    raise SystemExit(f"{backend} interactive mismatch ({label}): {result!r}")
            print(f"PASS: source interactive hosted/native agreement ({label})")


if __name__ == "__main__":
    main()
