#!/usr/bin/env python3
"""Direct native IO runtime tests; does not validate Fibril's C emitter/type checker."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / "runtime/native"
HARNESS = r'''
#include "fibril_runtime.h"
#include <stdlib.h>
#include <signal.h>

static int remaining;
static int bad_result;
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *text(FRuntime *r, FEnv *e) {
  static const unsigned char bytes[] = {108,105,110,101};
  (void)e; return f_literal(r, bytes, sizeof(bytes));
}
static FValue *unicode_text(FRuntime *r, FEnv *e) {
  static const unsigned char bytes[] = {206,187,32,240,159,140,141};
  (void)e; return f_literal(r, bytes, sizeof(bytes));
}
static FValue *write(FRuntime *r, FEnv *e) { return f_write(r, e, text); }
static FValue *chain(FRuntime *r, FEnv *e);
static FValue *consume(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *body(FRuntime *r, FEnv *e) { return f_unit_case(r, e, consume, chain); }
static FValue *next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, body); }
/* Trusted test fixture: a host counter generates descriptions. This is not
   source syntax or evidence of quantitative checking by the Fibril compiler. */
static FValue *chain(FRuntime *r, FEnv *e) {
  if (remaining-- > 0) return f_bind(r, e, write, next);
  return f_pure(r, e, bad_result ? text : unit);
}
static FValue *unicode_entry(FRuntime *r, FEnv *e) { return f_write(r, e, unicode_text); }
static FValue *last(FRuntime *r, FEnv *e) { return f_write(r, e, text); }
static FValue *ordered_body(FRuntime *r, FEnv *e) { return f_unit_case(r, e, consume, last); }
static FValue *ordered_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, ordered_body); }
static FValue *ordered(FRuntime *r, FEnv *e) { return f_bind(r, e, unicode_entry, ordered_next); }
int main(int argc, char **argv) {
  if (argc != 3) return 2;
  /* Observe represented stdio errors instead of process-level SIGPIPE death.
     Production signal policy is deliberately not changed by these tests. */
  signal(SIGPIPE, SIG_IGN);
  remaining = atoi(argv[1]); bad_result = atoi(argv[2]);
  return fibril_native_run(remaining == -1 ? unicode_entry : remaining == -2 ? ordered : chain);
}
'''


class NativeIORuntimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="fibril-native-io-")
        cls.addClassCleanup(cls.directory.cleanup)
        source = Path(cls.directory.name) / "io.c"
        source.write_text(HARNESS, encoding="utf-8")
        cls.executable = Path(cls.directory.name) / "io"
        subprocess.run(
            shlex.split(os.environ.get("CC", "cc")) + [
                "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(RUNTIME),
                str(source), str(RUNTIME / "fibril_runtime.c"), "-o", str(cls.executable),
            ], check=True, capture_output=True, timeout=60,
        )

    def run_plan(self, count, bad_result=0):
        return subprocess.run(
            [str(self.executable), str(count), str(bad_result)],
            capture_output=True, timeout=10,
        )

    def test_pure_unit_has_no_output(self):
        result = self.run_plan(0)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b"", b""))

    def test_bind_preserves_order(self):
        result = self.run_plan(-2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "λ 🌍\nline\n".encode())

    def test_utf8_output(self):
        result = self.run_plan(-1)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "λ 🌍\n".encode())

    def test_exact_write_limit(self):
        result = self.run_plan(64)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"line\n" * 64)

    def test_excess_writes_emit_no_prefix(self):
        result = self.run_plan(65)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"output action budget exhausted", result.stderr)

    @unittest.skipUnless(os.name == "posix", "requires POSIX pipe behavior")
    def test_broken_pipe_reports_flush_failure(self):
        reader, writer = os.pipe()
        os.close(reader)
        try:
            result = subprocess.run(
                [str(self.executable), "1", "0"], stdout=writer,
                stderr=subprocess.PIPE, timeout=10,
            )
        finally:
            os.close(writer)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"native stdout flush failed", result.stderr)

    def test_late_invalid_result_emits_no_prefix(self):
        result = self.run_plan(2, bad_result=1)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"main did not return unit", result.stderr)


if __name__ == "__main__":
    unittest.main()
