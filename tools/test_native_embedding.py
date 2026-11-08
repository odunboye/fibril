#!/usr/bin/env python3
"""Compile/run the trusted native embedding contract without an Idris build."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class NativeEmbeddingTests(unittest.TestCase):
    def test_contract(self):
        compiler = shlex.split(os.environ.get("CC", "cc"))
        scenarios = (
            "invalid", "pure", "text", "empty", "two-lines", "write-failure",
            "newline-failure", "flush-failure", "late-nul", "late-bad-final",
            "missing", "depth", "resource", "input", "nested", "mutated-table",
            "repeat",
        )
        with tempfile.TemporaryDirectory(prefix="fibril-embed-") as directory:
            executable = Path(directory) / "embed"
            subprocess.run([
                *compiler, "-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic",
                "-I", str(ROOT / "runtime/native"),
                str(ROOT / "test/native/embed.c"),
                str(ROOT / "runtime/native/fibril_runtime.c"),
                "-o", str(executable),
            ], check=True, timeout=60)
            for scenario in scenarios:
                with self.subTest(scenario=scenario):
                    result = subprocess.run([str(executable), scenario],
                                            capture_output=True, timeout=30)
                    self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
                    self.assertEqual(result.stdout, b"")
                    self.assertEqual(result.stderr, b"")
        print(f"Native embedding: {len(scenarios)} scenarios passed")


if __name__ == "__main__":
    unittest.main()
