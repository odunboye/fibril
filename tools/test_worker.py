#!/usr/bin/env python3
"""Checked request validation -> private buffering -> durable SQLite commit."""
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

from test_queue import sqlite_flags

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples/modules/queue-worker"
RUNTIME = ROOT / "runtime/native"


class WorkerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.build = tempfile.TemporaryDirectory(prefix="fibril-worker-build-")
        cls.addClassCleanup(cls.build.cleanup)
        work = Path(cls.build.name)
        cls.checked = work / "checked"
        cls.stub = work / "stub"
        cls.program = work / "validator.c"
        cls.command = [str(ROOT / "build/exec/fibril"), "--source-dir", str(SOURCE), str(SOURCE / "Main.fib")]
        emitted = subprocess.run([cls.command[0], "emit-c-binary", *cls.command[1:]],
                                 capture_output=True, check=True, timeout=60)
        cls.program.write_bytes(emitted.stdout)
        includes, libraries = sqlite_flags()
        common = [*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall", "-Wextra",
                  "-Werror", *includes, "-I", str(RUNTIME),
                  str(ROOT / "test/native/worker.c"), str(RUNTIME / "fibril_worker.c"),
                  str(RUNTIME / "fibril_queue.c")]
        subprocess.run([*common, "-DFIBRIL_EMBED_ONLY", str(cls.program),
                        str(RUNTIME / "fibril_binary_runtime.c"), "-o", str(cls.checked),
                        *libraries], check=True, timeout=60)
        subprocess.run([*common, "-DFW_STUB_VALIDATOR", "-o", str(cls.stub), *libraries],
                       check=True, timeout=60)
        cls.demo = work / "queue-worker"
        subprocess.run([*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall", "-Wextra",
                        "-Werror", *includes, "-DFIBRIL_EMBED_ONLY", "-I", str(RUNTIME),
                        str(ROOT / "examples/native/queue_worker.c"), str(RUNTIME / "fibril_worker.c"),
                        str(RUNTIME / "fibril_queue.c"), str(RUNTIME / "fibril_binary_runtime.c"),
                        str(cls.program), "-o", str(cls.demo), *libraries], check=True, timeout=60)
        cls.standalone = work / "validator"
        subprocess.run([*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall", "-Wextra",
                        "-Werror", "-I", str(RUNTIME), str(cls.program),
                        str(RUNTIME / "fibril_binary_runtime.c"), "-o", str(cls.standalone)],
                       check=True, timeout=60)

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="fibril-worker-")
        self.addCleanup(self.directory.cleanup)

    def run_fixture(self, mode, *args, stub=False, database="queue.db"):
        executable = self.stub if stub else self.checked
        result = subprocess.run([str(executable), str(mode), str(Path(self.directory.name) / database),
                                 *map(str, args)], capture_output=True, timeout=30)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b"", b""))

    def test_valid_enqueue_duplicate_conflict_and_tenant_scope(self):
        self.run_fixture("basic")

    def test_maximum_payload(self):
        self.run_fixture("maximum")

    def test_invalid_arguments_do_not_enqueue(self):
        self.run_fixture("invalid")

    def test_every_truncated_prefix_is_rejected(self):
        self.run_fixture("prefixes")

    def test_version_length_and_trailing_input_rejections(self):
        for reason in range(9):
            with self.subTest(reason=reason):
                self.run_fixture("reject", reason, database=f"reject-{reason}.db")

    def test_validated_output_is_not_acknowledgement_when_database_is_busy(self):
        self.run_fixture("locked")

    def test_exit_after_commit_before_acknowledgement_replays_same_row(self):
        self.run_fixture("crash")
        self.run_fixture("replay")

    def test_failed_partial_or_mismatched_validator_cannot_enqueue(self):
        for mode in range(9):
            with self.subTest(mode=mode):
                self.run_fixture(mode, stub=True, database=f"stub-{mode}.db")

    def test_local_demo_only_acknowledges_committed_requests(self):
        command = [str(self.demo), str(Path(self.directory.name) / "demo.db"), "trusted-scope"]
        packet = b"FQ01" + bytes(range(16)) + b"\x04\0\xff\r\n"
        first = subprocess.run(command, input=packet, capture_output=True, timeout=30)
        self.assertEqual((first.returncode, first.stderr), (0, b""))
        accepted = json.loads(first.stdout)
        self.assertEqual((accepted["status"], accepted["created"]), ("queued", True))
        duplicate = subprocess.run(command, input=packet, capture_output=True, timeout=30)
        self.assertEqual((duplicate.returncode, duplicate.stderr), (0, b""))
        replay = json.loads(duplicate.stdout)
        self.assertEqual((replay["id"], replay["created"]), (accepted["id"], False))
        for rejected in (packet[:-1] + b"x", packet[:-1], b"x" * 278):
            result = subprocess.run(command, input=rejected, capture_output=True, timeout=30)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b"")

    def test_hosted_native_validator_agreement(self):
        key = bytes(range(16))
        valid = [b"FQ01" + key + bytes([len(body)]) + body for body in
                 (b"\0", b"\0\xff\r\n", bytes(range(255)))]
        malformed = [b"", b"FQ02" + key + b"\x01x", b"FQ01" + key + b"\0",
                     b"FQ01" + key + b"\x02x", b"FQ01" + key + b"\x01xx",
                     b"FQ01" + key + b"\xff" + bytes(range(256))]
        for packet in valid + malformed:
            with self.subTest(length=len(packet), prefix=packet[:4]):
                hosted = subprocess.run([self.command[0], "run-binary", *self.command[1:]],
                                        input=packet, capture_output=True, timeout=60)
                native = subprocess.run([str(self.standalone)], input=packet,
                                        capture_output=True, timeout=30)
                if packet in valid:
                    expected = b"FV01" + packet[4:]
                    self.assertEqual((hosted.returncode, hosted.stdout, hosted.stderr), (0, expected, b""))
                    self.assertEqual((native.returncode, native.stdout, native.stderr), (0, expected, b""))
                else:
                    self.assertNotEqual(hosted.returncode, 0)
                    self.assertNotEqual(native.returncode, 0)
                    self.assertEqual((hosted.stdout, native.stdout), (b"", b""))


if __name__ == "__main__":
    unittest.main()
