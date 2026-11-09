#!/usr/bin/env python3
"""Native resource diagnostics: which limit stopped a program, and the opt-in stats line.

The budget diagnostic keeps its historical prefix and names the limit that was hit; FIBRIL_STATS=1
adds one stderr line (steps, peak depth, allocated bytes) and never changes stdout.
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

DOUBLE = '''double : (n : Nat) -> Nat
double n = natRec (\\(0 k : Nat) => Nat) Zero (\\(0 k : Nat) => \\(1 r : Nat) => Succ (Succ r)) n

'''
# natRec folds iteratively: 8192 successors cost many steps but little depth.
COUNT = DOUBLE + '''main : IO Unit
main = putStrLn (if primWordEq (primWordFromNat (double (double (double (double (double 256)))))) 8192w then "counted" else "wrong")
'''
# Non-tail recursion through a strict Word operand: depth grows with n.
HALF = 'module Main\n\n' + DOUBLE + '''count : (n : Nat) -> Word
count n = case n of
  Zero => 0w
  Succ p => primWordAdd 1w (count p)

main : IO Unit
main = putStrLn (if primWordEq (count (double (double (double 256)))) 2048w then "counted" else "wrong")
'''
SMALL = '''main : IO Unit
main = putStrLn "hello"
'''
STATS = re.compile(rb'fibril stats: steps=(\d+) peak_depth=(\d+) bytes=(\d+)\n')


class NativeStatsTests(unittest.TestCase):
    def build(self, source, directory, runtime=RUNTIME):
        # A source starting with "module" is a project (recursion needs one); else a single file.
        project = source.startswith('module ')
        root = Path(directory) / 'src'
        root.mkdir()
        path = root / 'Main.fib'
        path.write_text(source, encoding='utf-8')
        emitted = run_cli('emit-c', *(['--source-dir', str(root)] if project else []), str(path), timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        c_file, exe = Path(directory) / 'p.c', Path(directory) / 'p'
        c_file.write_text(emitted.stdout, encoding='utf-8')
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', '-I', str(runtime),
                                     str(c_file), str(runtime / 'fibril_runtime.c'), '-o', str(exe)],
                               capture_output=True, text=True, timeout=120)
        self.assertEqual(build.returncode, 0, build.stderr)
        return exe

    def run_exe(self, exe, stats):
        env = dict(os.environ)
        env.pop('FIBRIL_STATS', None)
        if stats is not None:
            env['FIBRIL_STATS'] = stats
        return subprocess.run([str(exe)], capture_output=True, env=env, timeout=60)

    def test_stats_are_opt_in_and_leave_stdout_alone(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(SMALL, directory)
            plain = self.run_exe(exe, None)
            self.assertEqual((plain.returncode, plain.stdout, plain.stderr), (0, b'hello\n', b''))
            for off in ('', '0'):
                self.assertEqual(self.run_exe(exe, off).stderr, b'')
            on = self.run_exe(exe, '1')
            self.assertEqual((on.returncode, on.stdout), (0, b'hello\n'))
            match = STATS.fullmatch(on.stderr)
            self.assertIsNotNone(match, on.stderr)
            steps, peak, allocated = map(int, match.groups())
            self.assertGreater(steps, 0)
            self.assertGreaterEqual(steps, peak)
            self.assertGreater(peak, 0)
            self.assertGreater(allocated, 0)

    def test_depth_limit_is_named_and_reported_with_stats(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(HALF, directory)
            result = self.run_exe(exe, '1')
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'native evaluation budget exhausted (depth limit)', result.stderr)
            self.assertNotIn(b'(step limit)', result.stderr)
            match = STATS.search(result.stderr)
            self.assertIsNotNone(match, result.stderr)
            self.assertEqual(int(match.group(2)), 512, 'the failing run peaks at the depth cap')
            self.assertLess(int(match.group(1)), 100000, 'steps were not what ran out')

    def test_step_limit_is_named_when_depth_is_not_the_problem(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(COUNT, directory)
            result = self.run_exe(exe, '1')
            self.assertEqual(result.returncode, 1)
            self.assertIn(b'native evaluation budget exhausted (step limit)', result.stderr)
            self.assertNotIn(b'(depth limit)', result.stderr)
            steps, peak, _ = map(int, STATS.search(result.stderr).groups())
            self.assertEqual(steps, 100000, 'stops at the step cap')
            self.assertLess(peak, 512, 'depth was not what ran out')


if __name__ == '__main__':
    unittest.main()
