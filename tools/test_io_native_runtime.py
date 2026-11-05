#!/usr/bin/env python3
"""Direct native IO runtime tests; does not validate Fibril's C emitter/type checker."""
import os
from pathlib import Path
import shlex
import selectors
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
static FValue *input_request(FRuntime *r, FEnv *e) { (void)e; return f_read_line(r); }
static FValue *eof_text(FRuntime *r, FEnv *e) {
  static const unsigned char bytes[] = {69,79,70};
  (void)e; return f_literal(r, bytes, sizeof(bytes));
}
static FValue *eof_branch(FRuntime *r, FEnv *e) { return f_write(r, e, eof_text); }
static FValue *payload_write(FRuntime *r, FEnv *e) { return f_write(r, e, consume); }
static FValue *payload_branch(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, payload_write); }
static FValue *input_case(FRuntime *r, FEnv *e) {
  FEval branches[] = {eof_branch, payload_branch, payload_branch};
  return f_variant_case(r, e, consume, 3, branches);
}
static FValue *input_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, input_case); }
static FValue *input_program(FRuntime *r, FEnv *e) { return f_bind(r, e, input_request, input_next); }
static FValue *prompt_body(FRuntime *r, FEnv *e) { return f_unit_case(r, e, consume, input_program); }
static FValue *prompt_next(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, prompt_body); }
static FValue *interactive(FRuntime *r, FEnv *e) { return f_bind(r, e, write, prompt_next); }
int main(int argc, char **argv) {
  if (argc != 3 && argc != 4) return 2;
  /* Observe represented stdio errors instead of process-level SIGPIPE death.
     Production signal policy is deliberately not changed by these tests. */
  signal(SIGPIPE, SIG_IGN);
  if (argc == 4) return fibril_native_interactive_run(interactive, (size_t)atoi(argv[1]), (size_t)atoi(argv[2]));
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

    def run_interactive(self, supplied, requests=3, limit=32):
        return subprocess.run(
            [str(self.executable), str(requests), str(limit), "interactive"],
            input=supplied, capture_output=True, timeout=10,
        )

    def test_interactive_unicode_crlf(self):
        result = self.run_interactive("λ 🌍\r\n".encode())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "line\nλ 🌍\n".encode())

    def test_interactive_prompt_is_flushed_before_input(self):
        process = subprocess.Popen(
            [str(self.executable), "3", "32", "interactive"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout, selectors.EVENT_READ)
                self.assertTrue(selector.select(timeout=5), "prompt blocked behind stdin")
            self.assertEqual(os.read(process.stdout.fileno(), 5), b"line\n")
            output, error = process.communicate(input=b"hello\n", timeout=5)
            self.assertEqual(process.returncode, 0, error)
            self.assertEqual(output, b"hello\n")
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()

    @unittest.skipUnless(os.name == "posix", "requires directory file descriptors")
    def test_interactive_read_error_is_not_eof(self):
        descriptor = os.open(self.directory.name, os.O_RDONLY)
        try:
            result = subprocess.run(
                [str(self.executable), "3", "32", "interactive"],
                stdin=descriptor, capture_output=True, timeout=10,
            )
        finally:
            os.close(descriptor)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"line\nConsole input failed\n")

    def test_interactive_eof(self):
        result = self.run_interactive(b"")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"line\nEOF\n")

    def test_interactive_empty_line_is_not_eof(self):
        result = self.run_interactive(b"\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"line\n\n")

    def test_interactive_preserves_unterminated_bare_cr(self):
        result = self.run_interactive(b"last\r")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"line\nlast\r\n")

    def test_interactive_length_error_is_a_result(self):
        result = self.run_interactive(b"toolong\n", limit=2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, b"line\nConsole input line length limit exceeded\n")

    def test_interactive_length_counts_unicode_characters(self):
        result = self.run_interactive("🌍🌍\n".encode(), limit=2)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "line\n🌍🌍\n".encode())

    def test_interactive_invalid_utf8_is_a_result(self):
        for supplied in [b"\xff\n", b"\xc0\x80\n", b"\xed\xa0\x80\n", b"\xf4\x90\x80\x80\n"]:
            with self.subTest(supplied=supplied):
                result = self.run_interactive(supplied)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, b"line\nConsole input is not valid UTF-8\n")

    def test_interactive_request_failure_can_leave_output(self):
        result = self.run_interactive(b"hello\n", requests=2)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, b"line\n")
        self.assertIn(b"interactive request budget exhausted", result.stderr)

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
