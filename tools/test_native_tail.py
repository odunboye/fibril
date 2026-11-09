#!/usr/bin/env python3
"""Native tail transfers: a tail call runs in constant evaluator depth, nothing else changes.

evaluate() runs a tail-position continuation in the same depth slot (see runtime/native/
fibril_runtime.c). These tests pin what must stay true: tail loops are depth-bounded, non-tail
recursion still stops at the depth limit, ignored arguments stay lazy, memoized thunks hold values,
and a cyclic thunk still fails.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

RUNTIME = ROOT / 'runtime/native'
CC = shlex.split(os.environ.get('CC', 'cc'))
STATS = re.compile(rb'fibril stats: steps=(\d+) peak_depth=(\d+) bytes=(\d+)')

HEADER = '''module Main

double : (n : Nat) -> Nat
double n = natRec (\\(0 k : Nat) => Nat) Zero (\\(0 k : Nat) => \\(1 r : Nat) => Succ (Succ r)) n

'''
# Steps down by two, which no single-step recursor expresses, so it is a real Fix.
LOOP = HEADER + '''loop : (n : Nat) -> Word
loop n = case n of
  Zero => 7w
  Succ a => case a of
    Zero => 7w
    Succ b => loop b

main : IO Unit
main = putStrLn (if primWordEq (loop (double (double (double 256)))) 7w then "done" else "wrong")
'''
# deep forces a depth-limit failure if it is ever evaluated; the loop only passes it along.
IGNORED = HEADER + '''deep : (n : Nat) -> Word
deep n = case n of
  Zero => 0w
  Succ p => primWordAdd 1w (deep p)

skip : (n : Nat) -> (ignored : Word) -> Word
skip n ignored = case n of
  Zero => 9w
  Succ a => case a of
    Zero => 9w
    Succ b => skip b ignored

main : IO Unit
main = putStrLn (if primWordEq (skip (double (double (double 256))) (deep (double (double (double 256))))) 9w then "lazy" else "wrong")
'''
# Not a tail call: the recursive result feeds a strict Word operand, so depth grows with n.
NON_TAIL = '''count : (n : Nat) -> Word
count n = case n of
  Zero => 0w
  Succ p => primWordAdd 1w (count p)

main : IO Unit
main = putStrLn (if primWordEq (count (double (double (double 256)))) 2048w then "counted" else "wrong")
'''
# The argument's code ends in a tail position and is used twice: its memoized value must be a value.
MEMO = '''twice : (x : Word) -> Word
twice x = primWordAdd x x

main : IO Unit
main = putStrLn (if primWordEq (twice (if primWordEq 1w 1w then 21w else 0w)) 42w then "memo" else "wrong")
'''
CYCLE = r'''#include "fibril_runtime.h"
/* A fixpoint whose body forces its own self cell before the closure exists. */
static FValue *self_reference(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *entry(FRuntime *r, FEnv *e) { (void)e; return f_fix(r, NULL, self_reference); }
int main(void) { return fibril_native_run(entry); }
'''


class NativeTailTests(unittest.TestCase):
    def compile(self, c_text, directory):
        c_file, exe = Path(directory) / 'p.c', Path(directory) / 'p'
        c_file.write_text(c_text, encoding='utf-8')
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', '-I', str(RUNTIME),
                                     str(c_file), str(RUNTIME / 'fibril_runtime.c'), '-o', str(exe)],
                               capture_output=True, text=True, timeout=120)
        self.assertEqual(build.returncode, 0, build.stderr)
        return exe

    def program(self, source, directory):
        root = Path(directory) / 'src'
        root.mkdir()
        path = root / 'Main.fib'
        path.write_text(source, encoding='utf-8')
        args = ['--source-dir', str(root)] if source.startswith('module ') else []
        emitted = run_cli('emit-c', *args, str(path), timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        return self.compile(emitted.stdout, directory)

    def run_exe(self, exe):
        env = dict(os.environ, FIBRIL_STATS='1')
        return subprocess.run([str(exe)], capture_output=True, env=env, timeout=60)

    def stats(self, result):
        match = STATS.search(result.stderr)
        self.assertIsNotNone(match, result.stderr)
        return tuple(map(int, match.groups()))

    def test_long_tail_loop_runs_in_bounded_depth(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_exe(self.program(LOOP, directory))
            self.assertEqual((result.returncode, result.stdout), (0, b'done\n'), result.stderr)
            steps, peak, _ = self.stats(result)
            self.assertLess(peak, 64, 'depth must not grow with the 2048 iterations')
            self.assertGreater(steps, 2048, 'the loop really ran')

    def test_non_tail_recursion_still_stops_at_the_depth_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_exe(self.program(HEADER + NON_TAIL, directory))
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'native evaluation budget exhausted (depth limit)', result.stderr)
            self.assertEqual(self.stats(result)[1], 512)

    def test_ignored_argument_stays_lazy_through_tail_calls(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_exe(self.program(IGNORED, directory))
            # Forcing the argument would recurse 2048 deep and hit the 512 depth limit.
            self.assertEqual((result.returncode, result.stdout), (0, b'lazy\n'), result.stderr)
            self.assertLess(self.stats(result)[1], 64)

    def test_memoized_tail_thunk_holds_a_value(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_exe(self.program(MEMO, directory))
            self.assertEqual((result.returncode, result.stdout), (0, b'memo\n'), result.stderr)

    def test_cyclic_thunk_still_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_exe(self.compile(CYCLE, directory))
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'cyclic native thunk', result.stderr)


if __name__ == '__main__':
    unittest.main()
