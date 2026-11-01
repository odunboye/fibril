#!/usr/bin/env python3
"""Check benchmark output structure/validation, never noisy timing thresholds."""
import json
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]


class BenchmarkTests(unittest.TestCase):
    def test_report_has_all_workloads_and_valid_samples(self):
        report = json.loads((ROOT / "build/benchmarks/latest.json").read_text())
        self.assertEqual(report["schema"], 1)
        self.assertEqual(report["code_generator"], "chez")
        self.assertTrue(report["source_sha256"])
        expected = {(case, size) for case in
                    ("substitution", "reduction", "erased", "runtime", "interval", "face")
                    for size in report["sizes"]}
        self.assertEqual({(r["workload"], r["size"]) for r in report["results"]}, expected)
        for row in report["results"]:
            self.assertEqual(len(row["raw_batch_ns"]), report["samples"])
            self.assertTrue(all(v >= 0 for v in row["raw_batch_ns"]))

    def test_driver_rejects_unsupported_or_unbounded_requests(self):
        executable = ROOT / "bench/build/exec/fibril-bench"
        for args in (("unknown", "2", "1"), ("interval", "7", "1"),
                     ("face", "0", "1"), ("erased", "2", "0")):
            with self.subTest(args=args):
                result = subprocess.run([str(executable), *args], capture_output=True,
                                        text=True, timeout=20)
                self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
