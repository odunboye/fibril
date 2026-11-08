#!/usr/bin/env python3
"""Public binary embedding contract; standalone trusted C fault tests."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class BinaryEmbeddingTests(unittest.TestCase):
    def test_contract(self):
        with tempfile.TemporaryDirectory(prefix="fibril-binary-embed-") as directory:
            executable = Path(directory) / "embed"
            subprocess.run([
                *shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall",
                "-Wextra", "-Werror", "-pedantic", "-I", str(ROOT / "runtime/native"),
                str(ROOT / "test/native/binary_embed.c"),
                str(ROOT / "runtime/native/fibril_binary_runtime.c"),
                "-o", str(executable),
            ], check=True, timeout=60)
            for mode in range(23):
                with self.subTest(mode=mode):
                    result = subprocess.run([str(executable), str(mode)],
                                            capture_output=True, timeout=30)
                    self.assertEqual((result.returncode, result.stdout, result.stderr),
                                     (0, b"", b""))
        print("Binary embedding: 23 scenarios passed")


if __name__ == "__main__":
    unittest.main()
