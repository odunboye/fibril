#!/usr/bin/env python3
"""Smoke-test the built CLI independently of its pure implementation helpers."""
from pathlib import Path
import subprocess
import tempfile
import random
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "build/exec/fibril"


def run(*args):
    return subprocess.run([str(EXE), *args], cwd=ROOT, text=True,
                          capture_output=True, timeout=20)


class CLITests(unittest.TestCase):
    def test_help(self):
        result = run("--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("fibril demo", result.stdout)
        self.assertIn("not implemented yet", result.stdout)

    def test_version(self):
        result = run("--version")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Fibril 0.1.0-dev", result.stdout)

    def test_demo(self):
        result = run("demo")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for expected in ("Identity type: (Pi 0 Type0 (Pi 1 v0 v1))",
                         "Erased checking: accepted", "closed usage []",
                         "Linear duplication: rejected", "De Morgan interval law: passed",
                         "disjoint, not exhaustive", "not a soundness proof"):
            self.assertIn(expected, result.stdout)

    def test_source_loader_accepts_valid_unicode_and_empty_files(self):
        for text in ("", "identity x = x", "λ x → x\r\n", "日本語 🌊", "\ufffd"):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.fib"
                path.write_bytes(text.encode("utf-8"))
                result = run("validate-source", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("not type checked", result.stdout)

    def test_source_loader_rejects_bad_bytes_and_controls(self):
        for data, expected in ((b"\xff", "byte 0"),
                               (b"A\xe2\x82A", "byte 3"),
                               (b"\xed\xa0\x80", "surrogate"),
                               (b"\xf4\x90\x80\x80", "U+10FFFF"),
                               (b"x\x00", "control"),
                               ("x\u202e".encode("utf-8"), "bidirectional"),
                               (b"\xef\xbb\xbf", "marks")):
            with self.subTest(data=data), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.fib"
                path.write_bytes(data)
                result = run("validate-source", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected, result.stdout)

    def test_source_loader_limits_and_missing_file(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.fib"
            path.write_bytes(b"a" * 65536)
            self.assertEqual(run("validate-source", str(path)).returncode, 0)
            path.write_bytes(b"a" * 65537)
            result = run("validate-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("limit", result.stdout)
            path.unlink()
            self.assertNotEqual(run("validate-source", str(path)).returncode, 0)

    def test_malformed_bytes_agree_with_python_strict_rejection(self):
        rng = random.Random(3629)
        malformed = []
        while len(malformed) < 30:
            data = bytes(rng.randrange(256) for _ in range(rng.randint(1, 6)))
            try:
                data.decode("utf-8", errors="strict")
            except UnicodeDecodeError:
                malformed.append(data)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.fib"
            for data in malformed:
                with self.subTest(data=data):
                    path.write_bytes(data)
                    result = run("validate-source", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("UTF-8", result.stdout)

    def test_lexer_command_reports_tokens_and_rejects_unsupported_text(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expression.fib"
            path.write_text("λ x ⇒ x", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("1:1-1:2 lambda", result.stdout)
            self.assertIn("1:5-1:6 =>", result.stdout)
            path.write_text("x @ y", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("1:3", result.stdout)

    def test_source_check_command(self):
        result = run("check", "examples/core/identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertIn("(Pi 0 Type0 (Pi 1 v0 v1))", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expression.fib"
            path.write_text("Type 0", encoding="utf-8")
            self.assertNotEqual(run("check", str(path)).returncode, 0)
            result = run("check", "--erased", str(path))
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("no runtime-use guarantee", result.stdout)
            self.assertIn("Type: Type1", result.stdout)
            path.write_text("missing", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Resolution: 1:1", result.stdout)
            path.write_text("Type", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Parsing:", result.stdout)

    def test_checked_reference_evaluation(self):
        path = "examples/core/evaluate-identity.fib"
        result = run("eval", path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("not compiled execution", result.stdout)
        self.assertIn("Normal: (Lam 1 Type0 v0)", result.stdout)
        result = run("eval", "--fuel", "0", path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("budget exhausted", result.stdout)
        self.assertNotIn("Normal:", result.stdout)
        result = run("eval", "--fuel", "0", "examples/core/identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout)
        for value in ("-1", "4097", "99999999999", "wrong"):
            with self.subTest(fuel=value):
                result = run("eval", "--fuel", value, path)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Fuel must", result.stdout)
        result = run("eval", "examples/core/identity-type.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Runtime", result.stdout)

    def test_unsupported_commands_fail(self):
        for args in (("build", "example.fib"), ("demo", "extra"), ("--unknown",)):
            with self.subTest(args=args):
                result = run(*args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Unsupported command", result.stdout)


if __name__ == "__main__":
    unittest.main()
