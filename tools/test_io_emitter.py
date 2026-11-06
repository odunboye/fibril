#!/usr/bin/env python3
"""Source -> checked C -> executable vs hosted plan; no project/YAML loading."""
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ["hello-world", "console-sequence", "io-functions", "do-let",
            "do-result", "string-append", "io-map"]
PROGRAM = r'''module EmitChecks

import Data.List
import System
import System.File
import Fibril.Core.Term
import Fibril.Source.File
import Fibril.Driver.Check
import Fibril.Driver.Console
import Fibril.Driver.Native.Emit
import Fibril.Effect.Console

fail : String -> IO ()
fail message = do putStrLn ("FAIL: " ++ message); exitFailure

emitExample : String -> String -> IO ()
emitExample directory name = do
  loaded <- readFile (directory ++ "/" ++ name ++ ".fib")
  case loaded of
    Left err => fail (show err)
    Right source => case resolveSource source of
      Left err => fail (show err)
      Right term => case (prepareIO 128 128 term, emitCheckedC term) of
        (Right actions, Right code) => do
          saved <- writeFile (directory ++ "/" ++ name ++ ".c") code
          expected <- writeFile (directory ++ "/" ++ name ++ ".expected")
            (concatMap (\(PrintLine text) => text ++ "\n") actions)
          case (saved, expected) of
            (Right (), Right ()) => pure ()
            _ => fail ("writing fixture " ++ name)
        (Left err, _) => fail (name ++ ": " ++ show err)
        (_, Left err) => fail (name ++ ": " ++ err)

main : IO ()
main = do
  directory <- getEnv "FIBRIL_IO_EMIT_FIXTURES"
  case directory of
    Nothing => fail "missing fixture directory"
    Just path => do
      traverse_ (emitExample path)
        ["hello-world", "console-sequence", "io-functions", "do-let",
         "do-result", "string-append", "io-map"]
      putStrLn "IO_EMISSION_OK"
'''


def main():
    env = os.environ.copy()
    if not env.get("CHEZ"):
        chez = shutil.which("chez") or shutil.which("scheme")
        if chez:
            env["CHEZ"] = chez
    with tempfile.TemporaryDirectory(prefix="fibril-io-emission-") as directory:
        work = Path(directory)
        (work / "Fibril").symlink_to(ROOT / "src/Fibril", target_is_directory=True)
        (work / "EmitChecks.idr").write_text(PROGRAM, encoding="utf-8")
        for name in EXAMPLES:
            shutil.copyfile(ROOT / "examples/core" / f"{name}.fib", work / f"{name}.fib")
        env["FIBRIL_IO_EMIT_FIXTURES"] = str(work)
        emitted = subprocess.run(
            shlex.split(env.get("IDRIS2", "idris2")) +
            ["--source-dir", ".", "EmitChecks.idr", "--exec", "main"],
            cwd=work, env=env, capture_output=True, text=True, timeout=180,
        )
        if emitted.returncode or "IO_EMISSION_OK" not in emitted.stdout:
            raise SystemExit(emitted.stdout + emitted.stderr)
        for name in EXAMPLES:
            executable = work / name
            subprocess.run(
                shlex.split(env.get("CC", "cc")) + [
                    "-std=c11", "-Wall", "-Wextra", "-Werror",
                    "-I", str(ROOT / "runtime/native"), str(work / f"{name}.c"),
                    str(ROOT / "runtime/native/fibril_runtime.c"), "-o", str(executable),
                ], check=True, capture_output=True, timeout=60,
            )
            result = subprocess.run([str(executable)], capture_output=True, timeout=10)
            expected = (work / f"{name}.expected").read_bytes()
            if result.returncode or result.stdout != expected or result.stderr:
                raise SystemExit(f"Native/hosted mismatch: {name}: {result!r}")
            print(f"PASS: checked C emission matches hosted plan ({name})")


if __name__ == "__main__":
    main()
