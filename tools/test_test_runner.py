#!/usr/bin/env python3
"""Check failure propagation and process-group cleanup in the suite runner."""
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from test_all import Runner, cli_shards
from test_units import ROOT, prepare_environment


class RunnerTests(unittest.TestCase):
    def test_cli_shards_cover_every_case_once(self):
        serial = cli_shards(1)
        parallel = cli_shards(8)
        names = [name for _, command in parallel for name in command[2:]]
        self.assertEqual(sorted(names), sorted(serial[0][1][2:]))
        self.assertEqual(len(names), len(set(names)))
        self.assertGreater(len(names), 0)

    def test_parallel_logs_and_failure_codes(self):
        with tempfile.TemporaryDirectory() as directory:
            runner = Runner(os.environ.copy(), directory)
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = [pool.submit(runner.run, name, [sys.executable, "-c", code])
                    for name, code in [("good", "print('good')"), ("bad", "print('bad'); exit(7)")]]
                results = [future.result() for future in futures]
            self.assertEqual([r["returncode"] for r in results], [0, 7])
            self.assertEqual((Path(directory) / "good.log").read_text(), "good\n")
            self.assertEqual((Path(directory) / "bad.log").read_text(), "bad\n")

    def test_timeout_kills_descendants(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / "orphan"
            child = f"import time,pathlib; time.sleep(1); pathlib.Path({str(marker)!r}).touch()"
            code = f"import subprocess,sys,time; subprocess.Popen([sys.executable,'-c',{child!r}]); time.sleep(20)"
            runner = Runner(os.environ.copy(), directory, timeout=0.2)
            result = runner.run("timeout", [sys.executable, "-c", code])
            self.assertEqual(result["returncode"], 124)
            self.assertTrue(result["timeout"])
            import time
            time.sleep(1.1)
            self.assertFalse(marker.exists())

    def test_cancel_prevents_queued_launches(self):
        with tempfile.TemporaryDirectory() as directory:
            runner = Runner(os.environ.copy(), directory)
            runner.cancel()
            result = runner.run("cancelled", ["this-command-must-not-launch"])
            self.assertEqual(result["returncode"], 130)

    def test_rejects_prepared_package_outside_worktree(self):
        with patch.dict(os.environ, {"FIBRIL_TEST_PACKAGE": "/tmp/stale-fibril"}):
            with self.assertRaisesRegex(SystemExit, "Invalid prepared"):
                prepare_environment()

    def test_prepared_children_do_not_reinstall(self):
        stage = ROOT / "build/test-prefix"
        stage.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=stage) as directory:
            (Path(directory) / "fibril.ipkg").touch()
            with patch.dict(os.environ, {"FIBRIL_TEST_PACKAGE": directory,
                                        "IDRIS2_PREFIX": str(stage)}):
                with patch("test_units.run") as command:
                    env = prepare_environment()
                    command.assert_not_called()
            self.assertEqual(env["FIBRIL_TEST_PACKAGE"], directory)

    def test_staging_filters_pack_warnings_and_shared_fibril(self):
        installed = ROOT / "build/test-prefix/idris2-test/fibril-0.1.0"
        outputs = ["cache warning\n/external/yaml/key/package:/external/fibril/key/package",
                   "cache warning\n/external/libs", "/external/data", str(installed), ""]
        with patch.dict(os.environ, {}, clear=True):
            with patch("test_units.run", side_effect=outputs) as command:
                env = prepare_environment(fresh=True)
        self.assertEqual(command.call_count, 5)
        self.assertEqual(env["IDRIS2_PACKAGE_PATH"],
                         str(installed.parent) + os.pathsep + "/external/yaml/key/package")
        self.assertEqual(env["IDRIS2_LIBS"], "/external/libs")


if __name__ == "__main__":
    unittest.main()
