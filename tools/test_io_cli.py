#!/usr/bin/env python3
"""Interactive IO tests against the complete built CLI, not a driver harness."""
import os
from pathlib import Path
import shlex
import signal
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "build/exec/fibril"
EXAMPLE = ROOT / "examples/core/read-line.fib"


def run_cli(*arguments, supplied=b""):
    process = subprocess.Popen(
        [str(EXE), *map(str, arguments)], stdin=subprocess.PIPE,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True,
    )
    try:
        output, error = process.communicate(input=supplied, timeout=20)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.communicate()
        raise
    return subprocess.CompletedProcess(process.args, process.returncode, output, error)


class InteractiveCLITests(unittest.TestCase):
    def test_help_exposes_explicit_modes(self):
        result = run_cli("--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"run-interactive PATH", result.stdout)
        self.assertIn(b"emit-c-interactive PATH", result.stdout)

    def test_real_source_input(self):
        result = run_cli("run-interactive", EXAMPLE, supplied="λ 🌍\r\n".encode())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "prompt\nreceived:λ 🌍\n".encode())
        self.assertEqual(result.stderr, b"")

    def test_source_eof(self):
        result = run_cli("run-interactive", EXAMPLE)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"prompt\nEOF\n")

    def test_preflighted_modes_reject_input_without_output(self):
        for command in ["run", "emit-c"]:
            with self.subTest(command=command):
                result = run_cli(command, EXAMPLE)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, b"")
                self.assertNotEqual(result.stderr, b"")

    def test_source_check_performs_no_requests(self):
        result = run_cli("check", EXAMPLE)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn(b"\nprompt\n", result.stdout)

    def test_invalid_source_rejected_before_first_write(self):
        with tempfile.TemporaryDirectory(prefix="fibril-cli-invalid-input-") as directory:
            source = Path(directory) / "Main.fib"
            source.write_text('main : IO Unit\nmain = do\n  putStrLn "must not print"\n  putStrLn True\n')
            result = run_cli("run-interactive", source)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b"")
            self.assertNotEqual(result.stderr, b"")

    def test_emitted_interactive_program_matches_cli(self):
        emitted = run_cli("emit-c-interactive", EXAMPLE)
        self.assertEqual(emitted.returncode, 0, emitted.stderr)
        self.assertIn(b"fibril_native_interactive_run", emitted.stdout)
        with tempfile.TemporaryDirectory(prefix="fibril-cli-native-input-") as directory:
            source = Path(directory) / "main.c"
            executable = Path(directory) / "main"
            source.write_bytes(emitted.stdout)
            subprocess.run(shlex.split(os.environ.get("CC", "cc")) + [
                "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(ROOT / "runtime/native"),
                str(source), str(ROOT / "runtime/native/fibril_runtime.c"), "-o", str(executable),
            ], check=True, capture_output=True, timeout=60)
            supplied = "λ 🌍\n".encode()
            native = subprocess.run([str(executable)], input=supplied, capture_output=True, timeout=10)
            hosted = run_cli("run-interactive", EXAMPLE, supplied=supplied)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(hosted.returncode, 0, hosted.stderr)
            self.assertEqual(native.stdout, hosted.stdout)

    def test_missing_interactive_path_rejected(self):
        for command in ["run-interactive", "emit-c-interactive"]:
            with self.subTest(command=command):
                self.assertNotEqual(run_cli(command).returncode, 0)


if __name__ == "__main__":
    unittest.main()
