#!/usr/bin/env python3
"""Trusted-C resource runtime tests. These fixtures bypass source typing/emission."""
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
HARNESS = r'''
#include "fibril_runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* Compile the runtime with fclose redirected, preserving real close but allowing
   deterministic status injection and exact-close counting. */
#ifdef fclose
#undef fclose
#endif
extern int fclose(FILE *);
#ifdef fopen
#undef fopen
#endif
extern FILE *fopen(const char *, const char *);
static int close_calls, open_calls, fail_close, mode;
FILE *tracked_open(const char *name, const char *kind) { open_calls++; return fopen(name, kind); }
static const char *filename;
static FValue *saved, *growing;
int tracked_close(FILE *file) { close_calls++; int status = fclose(file); return fail_close ? EOF : status; }
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *unit_io(FRuntime *r, FEnv *e) { return f_pure(r, e, unit); }
static FValue *v0(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *v1(FRuntime *r, FEnv *e) { return f_variable(r, e, 1); }
static FValue *v2(FRuntime *r, FEnv *e) { return f_variable(r, e, 2); }
static FValue *save0(FRuntime *r, FEnv *e) { saved = v0(r, e); return saved; }
static FValue *saved_value(FRuntime *r, FEnv *e) { (void)r; (void)e; return saved; }
static FValue *path(FRuntime *r, FEnv *e) {
  (void)e;
  if (mode == 31) {
    static unsigned char bytes[8192]; size_t n = strlen(filename);
    if (n + 2 > sizeof(bytes)) return NULL;
    memcpy(bytes, filename, n); bytes[n] = 0; bytes[n + 1] = 'x';
    return f_literal(r, bytes, n + 2);
  }
  return f_literal(r, (const unsigned char *)filename, strlen(filename));
}
static FValue *eof_text(FRuntime *r, FEnv *e) { (void)e; return f_literal(r, (const unsigned char *)"EOF", 3); }
static FValue *eof_write(FRuntime *r, FEnv *e) { return f_write(r, e, eof_text); }
static FValue *write0(FRuntime *r, FEnv *e) { return f_write(r, e, v0); }
static FValue *string_branch(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, write0); }
static FValue *read_result(FRuntime *r, FEnv *e) {
  FEval branches[] = {eof_write, string_branch, string_branch};
  return f_variant_case(r, e, v0, 3, branches);
}
static int reading(void) { return mode == 1 || mode == 2 || mode == 8 || mode == 10; }
static FValue *success_value(FRuntime *r, FEnv *e) {
  return reading() ? read_result(r, e) : f_unit_case(r, e, v0, unit_io);
}
static FValue *success_branch(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, success_value); }
static FValue *cleanup_second(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, write0); }
static FValue *cleanup_first(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, cleanup_second); }
static FValue *cleanup_case(FRuntime *r, FEnv *e) { return f_pair_case(r, e, v0, cleanup_first); }
static FValue *cleanup_branch(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, cleanup_case); }
static FValue *scope_case(FRuntime *r, FEnv *e) {
  FEval branches[] = {string_branch, success_branch, cleanup_branch};
  return f_variant_case(r, e, v0, 3, branches);
}
static FValue *after_scope(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, scope_case); }
static FValue *pair0(FRuntime *r, FEnv *e) { return f_pair(r, e, 0, 0, save0, unit); }
static FValue *pair1(FRuntime *r, FEnv *e) { return f_pair(r, e, 0, 0, v1, unit); }
static FValue *pair2(FRuntime *r, FEnv *e) { return f_pair(r, e, 0, 0, v2, unit); }
static FValue *read0(FRuntime *r, FEnv *e) { return f_read_input(r, e, v0); }
static FValue *read1(FRuntime *r, FEnv *e) { return f_read_input(r, e, v1); }
static FValue *stale_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, read1); }
static FValue *old_return(FRuntime *r, FEnv *e) { return f_pure(r, e, pair1); }
static FValue *old_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, old_return); }
static FValue *second_read(FRuntime *r, FEnv *e) { return f_read_input(r, e, v1); }
static FValue *read_second_field(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, second_read); }
static FValue *read_first_field(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, read_second_field); }
static FValue *unpack_read(FRuntime *r, FEnv *e) { return f_pair_case(r, e, v0, read_first_field); }
static FValue *threaded_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, unpack_read); }
static FValue *simple_return(FRuntime *r, FEnv *e) { return f_pure(r, e, mode == 12 ? pair2 : pair0); }
static FValue *simple_handle(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, simple_return); }
static FValue *simple_region(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, simple_handle); }
static FValue *nested(FRuntime *r, FEnv *e) { return f_with_input(r, e, path, simple_region); }
static FValue *nested_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, old_return); }
static FValue *loop(FRuntime *r, FEnv *e);
static FValue *loop_function(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, loop); }
static FValue *loop(FRuntime *r, FEnv *e) { return f_apply(r, e, loop_function, unit); }
static FValue *growing_value(FRuntime *r, FEnv *e) { (void)r; (void)e; return growing; }
static FValue *body(FRuntime *r, FEnv *e) {
  if (mode == 1 || mode == 8) return read0(r, e);
  if (mode == 2) return f_bind(r, e, read0, stale_next);
  if (mode == 3) return unit_io(r, e);
  if (mode == 4) return f_bind(r, e, read0, old_next);
  if (mode == 7 || mode == 12) return f_bind(r, e, nested, nested_next);
  if (mode == 10) return f_bind(r, e, read0, threaded_next);
  if (mode == 16) return loop(r, e);
  if (mode == 17) {
    growing = f_literal(r, (const unsigned char *)"x", 1);
    for (int i = 0; i < 32 && growing; i++) growing = f_append(r, e, growing_value, growing_value);
    return growing;
  }
  return f_pure(r, e, pair0);
}
static FValue *handle_body(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, body); }
static FValue *region_body(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, handle_body); }
static FValue *scope(FRuntime *r, FEnv *e) { return f_with_input(r, e, path, region_body); }
static FValue *revoked_read(FRuntime *r, FEnv *e) { return f_read_input(r, e, saved_value); }
static FValue *revoked_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, revoked_read); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_bind(r, e, scope, mode == 6 ? revoked_next : after_scope); }
static FValue *prefix(FRuntime *r, FEnv *e) { (void)e; return f_literal(r, (const unsigned char *)"prefix", 6); }
static FValue *prefix_write(FRuntime *r, FEnv *e) { return f_write(r, e, prefix); }
static FValue *prefix_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, entry); }
static FValue *prefixed(FRuntime *r, FEnv *e) { return f_bind(r, e, prefix_write, prefix_next); }
static FValue *trap(FRuntime *r, FEnv *e) { fputs("ERASED_FORCED\n", stderr); return unit(r, e); }
static FValue *kept(FRuntime *r, FEnv *e) { (void)e; return f_literal(r, (const unsigned char *)"kept", 4); }
static FValue *erased_pair(FRuntime *r, FEnv *e) { return f_pair(r, e, 1, 0, trap, kept); }
static FValue *erased_first(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, cleanup_second); }
static FValue *erased_entry(FRuntime *r, FEnv *e) { return f_pair_case(r, e, erased_pair, erased_first); }
int main(int argc, char **argv) {
  if (argc != 5) return 2;
  filename = argv[1]; mode = atoi(argv[2]); size_t requests = (size_t)atoi(argv[3]), limit = (size_t)atoi(argv[4]);
  if (mode == 20 || mode == 21 || mode == 23) {
    fail_close = 1; mode = mode == 20 ? 0 : mode == 21 ? 1 : 17;
  }
  int status = mode == 14 ? fibril_native_interactive_run(entry, requests, limit) :
               mode == 15 ? fibril_native_run(entry) :
               fibril_native_resource_run(mode == 8 ? prefixed : mode == 30 ? erased_entry : entry, requests, limit);
  fprintf(stderr, "OPEN_CALLS=%d\nCLOSE_CALLS=%d\n", open_calls, close_calls);
  return status;
}
'''


class NativeResourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="fibril-native-resources-")
        cls.addClassCleanup(cls.directory.cleanup)
        work = Path(cls.directory.name)
        source = work / "resources.c"
        source.write_text(HARNESS, encoding="utf-8")
        cls.executable = work / "resources"
        subprocess.run(shlex.split(os.environ.get("CC", "cc")) + [
            "-std=c11", "-Wall", "-Wextra", "-Werror", "-Dfclose=tracked_close", "-Dfopen=tracked_open",
            "-I", str(ROOT / "runtime/native"), str(source),
            str(ROOT / "runtime/native/fibril_runtime.c"), "-o", str(cls.executable),
        ], check=True, capture_output=True, timeout=60)

    def run_scope(self, mode=0, contents=b"hello\nsecond\n", requests=64, limit=8192, path=None):
        fixture = Path(self.directory.name) / "input.txt"
        fixture.write_bytes(contents)
        result = subprocess.run([
            str(self.executable), str(path or fixture), str(mode), str(requests), str(limit),
        ], capture_output=True, timeout=10)
        count = re.search(rb"CLOSE_CALLS=(\d+)", result.stderr)
        self.assertIsNotNone(count, result.stderr)
        return result, int(count[1])

    def assert_failure_closed(self, mode, message, requests=64):
        result, closes = self.run_scope(mode, requests=requests)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(message, result.stderr)
        self.assertEqual(closes, 1)
        return result

    def test_scope_returns_ownership_and_closes(self):
        result, closes = self.run_scope()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((result.stdout, closes), (b"", 1))

    def test_pair_erased_field_is_not_evaluated(self):
        result, closes = self.run_scope(30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((result.stdout, closes), (b"kept\n", 0))
        self.assertNotIn(b"ERASED_FORCED", result.stderr)

    def test_nul_path_rejected_before_open(self):
        result, closes = self.run_scope(31)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"File open failed: NUL in path\n")
        self.assertIn(b"OPEN_CALLS=0", result.stderr)
        self.assertEqual(closes, 0)

    def test_owned_read_unicode_crlf(self):
        result, closes = self.run_scope(1, "λ 🌍\r\n".encode())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((result.stdout, closes), ("λ 🌍\n".encode(), 1))

    def test_owned_read_eof_and_empty_line(self):
        for contents, expected in [(b"", b"EOF\n"), (b"\n", b"\n")]:
            with self.subTest(contents=contents):
                result, closes = self.run_scope(1, contents)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual((result.stdout, closes), (expected, 1))

    def test_two_reads_thread_successor_ownership(self):
        result, closes = self.run_scope(10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((result.stdout, closes), (b"second\n", 1))

    def test_read_error_returns_successor_and_closes(self):
        result, closes = self.run_scope(1, b"long\n", limit=2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"File read failed: Console input line length limit exceeded\n")
        self.assertEqual(closes, 1)

    def test_stale_read_rejected_and_closed(self):
        self.assert_failure_closed(2, b"Stale input reference")

    def test_stale_return_rejected_and_closed(self):
        self.assert_failure_closed(4, b"did not return current ownership")

    def test_revoked_reference_rejected_without_double_close(self):
        self.assert_failure_closed(6, b"Revoked input reference")

    def test_missing_ownership_pair_rejected_and_closed(self):
        self.assert_failure_closed(3, b"did not return an ownership pair")

    def test_request_failure_still_closes(self):
        self.assert_failure_closed(1, b"request budget exhausted", requests=1)

    def test_zero_requests_prevents_open(self):
        result, closes = self.run_scope(0, requests=0)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"request budget exhausted", result.stderr)
        self.assertEqual(closes, 0)
        self.assertIn(b"OPEN_CALLS=0", result.stderr)

    def test_allocation_failure_still_closes(self):
        self.assert_failure_closed(17, b"allocation budget exhausted")

    def test_evaluation_failure_still_closes(self):
        self.assert_failure_closed(16, b"evaluation budget exhausted")

    def test_nested_scopes_close_each_file_once(self):
        result, closes = self.run_scope(7)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(closes, 2)

    def test_nested_region_swap_closes_both(self):
        result, closes = self.run_scope(12)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"did not return current ownership", result.stderr)
        self.assertEqual(closes, 2)

    def test_open_failure_does_not_close_or_call_body(self):
        result, closes = self.run_scope(17, path=Path(self.directory.name) / "missing")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"File open failed:", result.stdout)
        self.assertEqual(closes, 0)

    def test_close_failure_preserves_result_and_is_not_retried(self):
        result, closes = self.run_scope(20)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, b"File close failed\n")
        self.assertIn(b"fibril native cleanup: File close failed", result.stderr)
        self.assertEqual(closes, 1)

    def test_primary_and_close_failures_are_both_reported(self):
        result, closes = self.run_scope(21, requests=1)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"request budget exhausted", result.stderr)
        self.assertIn(b"fibril native cleanup: File close failed", result.stderr)
        self.assertEqual(closes, 1)

    def test_allocation_and_close_failures_are_both_reported(self):
        result, closes = self.run_scope(23)
        self.assertEqual(result.returncode, 1)
        self.assertIn(b"allocation budget exhausted", result.stderr)
        self.assertIn(b"fibril native cleanup: File close failed", result.stderr)
        self.assertEqual(closes, 1)

    def test_interactive_and_preflight_runners_do_not_open_files(self):
        for mode in [14, 15]:
            with self.subTest(mode=mode):
                result, closes = self.run_scope(mode)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(closes, 0)
                self.assertIn(b"OPEN_CALLS=0", result.stderr)

    def test_late_failure_may_preserve_output_prefix(self):
        result = self.assert_failure_closed(8, b"request budget exhausted", requests=2)
        self.assertEqual(result.stdout, b"prefix\n")


if __name__ == "__main__":
    unittest.main()
