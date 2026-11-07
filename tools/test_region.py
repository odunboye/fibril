#!/usr/bin/env python3
"""Native sub-arena (withRegion) tests: reclamation, copy-out and thunk memoization.

C is compiled with AddressSanitizer so a dangling pointer into a freed region fails
the run rather than passing by luck. These are sampled checks, not a safety proof."""
from pathlib import Path
import os
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

RUNTIME = ROOT / 'runtime/native'
CC = shlex.split(os.environ.get('CC', 'cc'))
SANITIZE = ['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g']

HARNESS = r'''
#include "fibril_runtime.h"
#include <stdio.h>
#include <stdlib.h>
static unsigned char block[32768];
static FValue *chunk(FRuntime *r, FEnv *e) { (void)e; return f_bytes_literal(r, block, sizeof(block)); }
/* Allocate about 100 KiB, then return only a Bool. */
static FValue *region_inner(FRuntime *r, FEnv *e) {
  FValue *x = f_bytes_append(r, e, chunk, chunk);
  FValue *y = x ? f_bytes_append(r, e, chunk, chunk) : NULL;
  return y ? f_bool(r, 1) : NULL;
}
static FValue *region_body(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, region_inner); }
static FValue *with_region(FRuntime *r, FEnv *e) { return f_with_region(r, e, region_body); }
static FValue *plain(FRuntime *r, FEnv *e) { return region_inner(r, e); }
static int iterations;
static int use_region;
static FValue *text(FRuntime *r, FEnv *e) {
  static const unsigned char ok[] = {'o', 'k'};
  for (int i = 0; i < iterations; i++)
    if (!(use_region ? with_region(r, e) : plain(r, e))) return NULL;
  return f_literal(r, ok, sizeof(ok));
}
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, text); }
int main(int argc, char **argv) {
  if (argc != 3) return 2;
  iterations = atoi(argv[1]); use_region = atoi(argv[2]);
  return fibril_native_run(entry);
}
'''


def build(sources, out):
    done = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic'] + SANITIZE +
                          ['-I', str(RUNTIME)] + [str(s) for s in sources] + [str(RUNTIME / 'fibril_runtime.c'),
                          '-o', str(out)], capture_output=True, text=True, timeout=180)
    assert done.returncode == 0, done.stdout + done.stderr


class RegionRuntimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        source = Path(cls.directory.name) / 'harness.c'
        source.write_text(HARNESS)
        cls.binary = Path(cls.directory.name) / 'harness'
        build([source], cls.binary)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def run_harness(self, iterations, region):
        return subprocess.run([str(self.binary), str(iterations), str(region)], capture_output=True, text=True, timeout=120)

    def test_regions_reclaim_budget_that_one_arena_exhausts(self):
        # ~200 KiB per iteration: 2000 of them is far above the 16 MiB payload cap.
        plain = self.run_harness(2000, 0)
        self.assertNotEqual(plain.returncode, 0)
        self.assertIn('allocation budget exhausted', plain.stderr)
        scoped = self.run_harness(2000, 1)
        self.assertEqual((scoped.returncode, scoped.stdout, scoped.stderr), (0, 'ok\n', ''))


class RegionSourceTests(unittest.TestCase):
    def compile_and_run(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            args = ['--source-dir', directory, str(path)]
            emitted = run_cli('emit-c', *args, timeout=120)
            self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
            c_file = Path(directory) / 'program.c'
            c_file.write_text(emitted.stdout, encoding='utf-8')
            build([c_file], Path(directory) / 'program')
            native = subprocess.run([str(Path(directory) / 'program')], capture_output=True, text=True, timeout=120)
            reference = run_cli('run', *args, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stdout + reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, reference.stdout)
            return native.stdout

    def test_string_result_is_copied_out(self):
        out = self.compile_and_run('module Main\nmain : IO Unit\n'
            'main = putStrLn (primWithRegion String (\\(0 r : Type 0) => appendString (appendString "hello" ", ") "region"))\n')
        self.assertEqual(out, 'hello, region\n')

    def test_nat_result_and_nesting(self):
        out = self.compile_and_run('module Main\n'
            'marks : (1 n : Nat) -> String\n'
            'marks n = natRec (\\(0 k : Nat) => String) "" (\\(0 k : Nat) => \\(1 result : String) => appendString result "!") n\n'
            'main : IO Unit\n'
            'main = putStrLn (marks (primWithRegion Nat (\\(0 r : Type 0) => Succ (primWithRegion Nat (\\(0 s : Type 0) => Succ (Succ Zero))))))\n')
        self.assertEqual(out, '!!!\n')

    def test_outer_thunk_forced_inside_region_stays_valid_after_exit(self):
        # s is forced inside the region but used again afterwards; its memo must live in the parent.
        out = self.compile_and_run('module Main\n'
            'both : (s : String) -> String\n'
            'both = \\(s : String) => appendString (primWithRegion String (\\(0 r : Type 0) => appendString s "-in")) s\n'
            'main : IO Unit\n'
            'main = putStrLn (both (appendString "a" "b"))\n')
        self.assertEqual(out, 'ab-inab\n')

    def test_function_result_fails_closed_at_runtime(self):
        # The primitive is generic in B and its type argument is a bound variable by the
        # time the entry is checked, so a function result is caught by the runtime copy.
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\nf : Bool -> Bool\n'
                'f = primWithRegion (Bool -> Bool) (\\(0 r : Type 0) => \\(b : Bool) => b)\n'
                'main : IO Unit\nmain = putStrLn (if f True then "x" else "y")\n')
            args = ['--source-dir', directory, str(path)]
            emitted = run_cli('emit-c', *args, timeout=120)
            self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
            c_file = Path(directory) / 'program.c'
            c_file.write_text(emitted.stdout, encoding='utf-8')
            build([c_file], Path(directory) / 'program')
            native = subprocess.run([str(Path(directory) / 'program')], capture_output=True, text=True, timeout=120)
            self.assertEqual(native.returncode, 1)
            self.assertEqual(native.stdout, '')
            self.assertIn('first-order data', native.stderr)

    def test_region_cannot_escape_through_the_result_type(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\n'
                'main : IO Unit\n'
                'main = putStrLn (primWithRegion (Type 0) (\\(0 r : Type 0) => r))\n')
            result = run_cli('emit-c', '--source-dir', directory, str(path), timeout=120)
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main()
