#!/usr/bin/env python3
"""Compare the private host compiler with the stock pinned checker."""
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import unittest

import fibril_idris

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = {
    "structural": (True, """count : Nat -> Nat
count Z = Z
count (S n) = S (count n)
"""),
    "swapped_mutual": (True, """mutual
  left : Nat -> Nat -> Nat
  left Z m = m
  left (S n) m = right m n
  right : Nat -> Nat -> Nat
  right m n = left n m
"""),
    "local_mutual": (True, """descend : Nat -> Nat
descend x = go x
  where
    go : Nat -> Nat
    go Z = Z
    go (S n) = descend n
"""),
    "direct_loop": (False, """loop : Nat -> Nat
loop n = loop n
"""),
    "mutual_loop": (False, """mutual
  left : Nat -> Nat -> Nat
  left Z m = m
  left (S n) m = right m (S n)
  right : Nat -> Nat -> Nat
  right m n = left n m
"""),
    "local_loop": (False, """descend : Nat -> Nat
descend x = go x
  where
    go : Nat -> Nat
    go Z = Z
    go (S n) = descend (S n)
"""),
}


def run(command, cwd, env):
    process = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               start_new_session=True)
    try:
        output, _ = process.communicate(timeout=60)
        return process.returncode, output
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()


class HostCompilerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.stock, cls.paths, cls.env = fibril_idris.pinned_context()
        cls.fast = str(fibril_idris.ensure_compiler(cls.stock, cls.paths, cls.env))

    def test_same_totality_decisions_diagnostics_and_checked_interfaces(self):
        with tempfile.TemporaryDirectory(prefix="fibril-host-") as directory:
            root = Path(directory)
            source = root / "Fixture.idr"
            for name, (accepted, body) in FIXTURES.items():
                with self.subTest(name=name):
                    source.write_text("module Fixture\n\n%default total\n\n" + body)
                    results = []
                    for label, compiler in (("stock", self.stock), ("fast", self.fast)):
                        cache = root / name / label
                        result = run([compiler, "--no-color", "--source-dir", str(root),
                                      "--build-dir", str(cache), "--check", str(source)],
                                     root, self.env)
                        self.assertEqual(result[0] == 0, accepted, result[1])
                        if not accepted:
                            self.assertIn("not total", result[1].lower())
                        results.append(result)
                    self.assertEqual(results[0], results[1], "Checker diagnostics changed")
                    if accepted:
                        stock_ttc = list((root / name / "stock").rglob("Fixture.ttc"))
                        fast_ttc = list((root / name / "fast").rglob("Fixture.ttc"))
                        self.assertEqual(len(stock_ttc), 1)
                        self.assertEqual(len(fast_ttc), 1)
                        self.assertEqual(stock_ttc[0].read_bytes(), fast_ttc[0].read_bytes())

    def test_caller_private_prefix_and_package_path_are_preserved(self):
        with tempfile.TemporaryDirectory(prefix="fibril-host-prefix-") as directory:
            root = Path(directory)
            library = root / "library"
            consumer = root / "consumer"
            library.mkdir()
            consumer.mkdir()
            (library / "sentinel.ipkg").write_text(
                'package sentinel\nversion = 0.0.0\nsourcedir = "."\nmodules = Sentinel\n')
            (library / "Sentinel.idr").write_text(
                'module Sentinel\npublic export\nmarker : Nat\nmarker = Z\n')
            env = self.env.copy()
            env["IDRIS2_PREFIX"] = str(root / "private-prefix")
            code, output = run([self.stock, "--install", "sentinel.ipkg"], library, env)
            self.assertEqual(code, 0, output)
            code, output = run([self.stock, "--dump-installdir", "sentinel.ipkg"], library, env)
            self.assertEqual(code, 0, output)
            installed = Path(output.strip())
            self.assertTrue(installed.is_relative_to(root / "private-prefix"))
            env["IDRIS2_PACKAGE_PATH"] = os.pathsep.join(
                [str(installed.parent), self.paths["IDRIS2_PACKAGE_PATH"]])
            (consumer / "consumer.ipkg").write_text(
                'package consumer\nsourcedir = "."\ndepends = sentinel\nmodules = Consumer\n')
            (consumer / "Consumer.idr").write_text(
                'module Consumer\nimport Sentinel\npublic export\nactual : Nat\nactual = marker\n')
            code, output = run([str(ROOT / "tools/fibril_idris.py"), "--typecheck", "consumer.ipkg"],
                               consumer, env)
            self.assertEqual(code, 0, output)

    def test_unknown_compiler_source_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "Unsupported Idris"):
            fibril_idris.lazy_traces("module UnrecognizedCompiler\n")


if __name__ == "__main__":
    unittest.main()
