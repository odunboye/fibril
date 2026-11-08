#!/usr/bin/env python3
"""Trusted SQLite enqueue boundary: persistence, conflicts, crashes and locks."""
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import shlex
import shutil
import sqlite3
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def sqlite_flags():
    if "SQLITE_CFLAGS" in os.environ or "SQLITE_LIBS" in os.environ:
        return shlex.split(os.environ.get("SQLITE_CFLAGS", "")), shlex.split(os.environ.get("SQLITE_LIBS", "-lsqlite3"))
    if shutil.which("pkg-config"):
        return (shlex.split(subprocess.check_output(["pkg-config", "--cflags", "sqlite3"], text=True)),
                shlex.split(subprocess.check_output(["pkg-config", "--libs", "sqlite3"], text=True)))
    return [], ["-lsqlite3"]


class QueueTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.build = tempfile.TemporaryDirectory(prefix="fibril-queue-build-")
        cls.executable = Path(cls.build.name) / "queue"
        includes, libraries = sqlite_flags()
        try:
            subprocess.run([
                *shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall", "-Wextra",
                "-Werror", "-pedantic", *includes, "-I", str(ROOT / "runtime/native"),
                str(ROOT / "test/native/queue.c"), str(ROOT / "runtime/native/fibril_queue.c"),
                "-o", str(cls.executable), *libraries,
            ], check=True, timeout=60)
        except BaseException:
            cls.build.cleanup()
            raise

    @classmethod
    def tearDownClass(cls):
        cls.build.cleanup()

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="fibril-queue-")
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "queue.db"

    def run_mode(self, mode, *args, output=False):
        result = subprocess.run([str(self.executable), mode, str(self.path), *map(str, args)],
                                capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        self.assertEqual(result.stderr, b"")
        if not output:
            self.assertEqual(result.stdout, b"")
        return result.stdout

    def test_binary_idempotency_conflict_tenant_scope_and_reopen(self):
        self.run_mode("basic")
        with sqlite3.connect(self.path) as connection:
            self.assertEqual(connection.execute("SELECT count(*) FROM fibril_queue").fetchone()[0], 3)
            self.assertEqual(connection.execute("PRAGMA user_version").fetchone()[0], 1)
            self.assertEqual(connection.execute("PRAGMA journal_mode").fetchone()[0], "wal")
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o600)

    def test_invalid_arguments_and_request_bounds(self):
        self.run_mode("invalid")

    def test_maximum_binary_request(self):
        self.run_mode("maximum")

    def test_lock_contention_is_explicit_and_retryable(self):
        self.run_mode("locked")

    def test_abandoned_uncommitted_transaction_is_not_accepted(self):
        self.run_mode("init")
        self.run_mode("crash-uncommitted")
        self.run_mode("absent")
        self.assertTrue(self.run_mode("enqueue", output=True).strip().endswith(b" 1"))

    def test_committed_before_acknowledgement_survives_process_exit(self):
        self.run_mode("crash-committed")
        self.run_mode("exists")
        self.assertTrue(self.run_mode("enqueue", output=True).strip().endswith(b" 0"))

    def test_concurrent_same_key_creates_exactly_one_queue_row(self):
        self.run_mode("init")
        with ThreadPoolExecutor(max_workers=4) as pool:
            outputs = list(pool.map(lambda _: self.run_mode("enqueue", output=True), range(12)))
        parsed = [tuple(map(int, out.split())) for out in outputs]
        self.assertEqual(len({row for row, _ in parsed}), 1)
        self.assertEqual(sum(created for _, created in parsed), 1)
        with sqlite3.connect(self.path) as connection:
            self.assertEqual(connection.execute("SELECT count(*) FROM fibril_queue").fetchone()[0], 1)

    def test_foreign_database_is_not_adopted_or_rejournaled(self):
        with sqlite3.connect(self.path) as connection:
            connection.execute("CREATE TABLE sqlitex_foreign(value)")
            connection.execute("INSERT INTO sqlitex_foreign VALUES('retained')")
        self.path.chmod(0o600)
        self.run_mode("open-status", 7)  # FQ_UNSUPPORTED
        with sqlite3.connect(self.path) as connection:
            self.assertEqual(connection.execute("PRAGMA journal_mode").fetchone()[0], "delete")
            self.assertEqual(connection.execute("SELECT value FROM sqlitex_foreign").fetchone()[0], "retained")

    def test_unknown_version_is_rejected(self):
        self.run_mode("init")
        with sqlite3.connect(self.path) as connection:
            connection.execute("PRAGMA user_version=99")
        self.run_mode("open-status", 7)

    def test_counterfeit_schema_and_added_trigger_are_rejected(self):
        with sqlite3.connect(self.path) as connection:
            connection.executescript("CREATE TABLE fibril_queue(id,tenant,key,payload); PRAGMA user_version=1;")
        self.path.chmod(0o600)
        self.run_mode("open-status", 7)
        self.path.unlink()
        self.run_mode("init")
        with sqlite3.connect(self.path) as connection:
            connection.execute("CREATE TRIGGER surprise AFTER INSERT ON fibril_queue BEGIN DELETE FROM fibril_queue; END")
        self.run_mode("open-status", 7)

    def test_corrupt_database_is_storage_error_not_empty_queue(self):
        self.path.write_bytes(b"not a sqlite database" * 100)
        self.path.chmod(0o600)
        self.run_mode("open-status", 6)  # FQ_STORAGE

    def test_symlink_hardlink_directory_and_permissions_are_rejected(self):
        target = self.path.with_name("target.db")
        target.touch(mode=0o600)
        self.path.symlink_to(target)
        self.run_mode("open-status", 1)
        self.path.unlink()
        os.link(target, self.path)
        self.run_mode("open-status", 1)
        self.path.unlink()
        self.path.mkdir()
        self.run_mode("open-status", 6)
        self.path.rmdir()
        self.path.touch(mode=0o644)
        self.path.chmod(0o644)
        self.run_mode("open-status", 1)


if __name__ == "__main__":
    unittest.main()
