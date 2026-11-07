#!/usr/bin/env python3
"""Checked source records, raw core mode/admission checks, and raw pair laziness.

Set FIBRIL_PAIR_SANITIZE=1 to compile every C fixture with ASan and UBSan.
No shared package installation is used by the raw-core observer.
"""
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

RUNTIME = ROOT / 'runtime/native'
EXAMPLES = ROOT / 'examples/modules/native-pairs'
CC = shlex.split(os.environ.get('CC', 'cc'))
SANITIZERS = (['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g']
              if os.environ.get('FIBRIL_PAIR_SANITIZE') == '1' else [])

RAW_OBSERVER = r'''module PairCompare
import Data.List
import System
import System.File
import Fibril.Core.Quantity
import Fibril.Core.Term
import Tests.PairEmission

fail : String -> IO ()
fail message = do
  _ <- fPutStrLn stderr message
  exitFailure

quantities : List (String, Quantity)
quantities = [("erased", Erased), ("linear", Linear), ("unrestricted", Unrestricted)]

main : IO ()
main = do
  traverse_ (\(label, ok) => putStrLn ((if ok then "PASS: " else "FAIL: ") ++ label)) checks
  if not (all snd checks) then exitFailure else pure ()
  target <- getEnv "FIBRIL_PAIR_OUTPUT"
  case target of
    Nothing => fail "missing pair output directory"
    Just directory => traverse_ (\(mode, emit) =>
      traverse_ (\(first, q) => traverse_ (\(second, r) =>
        case emit (pairEntry q r) of
          Left err => fail (mode ++ ": " ++ err)
          Right code => do
            written <- writeFile (directory ++ "/" ++ mode ++ "-" ++ first ++ "-" ++ second ++ ".c") code
            case written of
              Left err => fail (show err)
              Right () => pure ()) quantities) quantities) emitters
'''

# A raw runtime probe is not source-language or typing evidence. The poison
# callback makes forcing an erased/unused field or a dormant branch observable.
RAW_LAZINESS = r'''#include "fibril_runtime.h"
#include <stdlib.h>
static FValue *poison(FRuntime *r, FEnv *e) { (void)r; (void)e; abort(); }
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *done(FRuntime *r, FEnv *e) { return f_pure(r, e, unit); }
static FValue *second(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *first(FRuntime *r, FEnv *e) { return f_variable(r, e, 1); }
static FValue *take_second(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, second); }
static FValue *take_first(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, first); }
static FValue *branch_second(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, take_second); }
static FValue *branch_first(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, take_first); }
static FValue *unused_second(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, second); }
static FValue *branch_unused(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, unused_second); }
static FValue *erased_first(FRuntime *r, FEnv *e) { return f_pair(r, e, 1, 0, poison, done); }
static FValue *erased_second(FRuntime *r, FEnv *e) { return f_pair(r, e, 0, 1, done, poison); }
static FValue *unused_first(FRuntime *r, FEnv *e) { return f_pair(r, e, 0, 0, poison, done); }
static FValue *yes(FRuntime *r, FEnv *e) { (void)e; return f_bool(r, 1); }
static FValue *selected(FRuntime *r, FEnv *e) { return f_bool_case(r, e, yes, done, poison); }
static FValue *pair_branch(FRuntime *r, FEnv *e) { return f_pair(r, e, 0, 0, poison, selected); }
static FValue *entry_a(FRuntime *r, FEnv *e) { return f_pair_case(r, e, erased_first, branch_second); }
static FValue *entry_b(FRuntime *r, FEnv *e) { return f_pair_case(r, e, erased_second, branch_first); }
static FValue *entry_c(FRuntime *r, FEnv *e) { return f_pair_case(r, e, unused_first, branch_unused); }
static FValue *entry_d(FRuntime *r, FEnv *e) { return f_pair_case(r, e, pair_branch, branch_unused); }
int main(void) {
  return fibril_native_run(entry_a) || fibril_native_run(entry_b) ||
         fibril_native_run(entry_c) || fibril_native_run(entry_d);
}
'''


class NativePairTests(unittest.TestCase):
    def compile_run(self, code, directory, *, binary=False, supplied=b'', name='program'):
        source = Path(directory) / (name + '.c')
        executable = Path(directory) / name
        source.write_text(code)
        runtime = 'fibril_binary_runtime.c' if binary else 'fibril_runtime.c'
        built = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
            *SANITIZERS, '-I', str(RUNTIME), str(source), str(RUNTIME / runtime),
            '-o', str(executable)], capture_output=True, timeout=120)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        result = subprocess.run([str(executable)], input=supplied, capture_output=True, timeout=30)
        return result

    def test_checked_source_nested_mixed_records_preflight_and_binary(self):
        for entry, emit, run, expected in [
            ('Main', 'emit-c', 'run', b'pair!!tail\n'),
            ('Binary', 'emit-c-binary', 'run-binary', b'pair!!tail')]:
            args = ['--source-dir', str(EXAMPLES), str(EXAMPLES / (entry + '.fib'))]
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as directory:
                checked = run_cli('check', *args, timeout=120)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                hosted = run_cli(run, *args, text=False, timeout=120)
                emitted = run_cli(emit, *args, timeout=120)
                self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
                self.assertIn('f_pair(', emitted.stdout)
                self.assertIn('f_pair_case(', emitted.stdout)
                native = self.compile_run(emitted.stdout, directory, binary=entry == 'Binary')
                for result in (hosted, native):
                    self.assertEqual((result.returncode, result.stdout, result.stderr), (0, expected, b''))

    def test_checked_source_dependent_erased_type_record(self):
        root = ROOT / 'examples/modules/records'
        for entry, expected in [('Main', b'Records!\n'), ('Patterns', b'Patterns!\n')]:
            args = ['--source-dir', str(root), str(root / (entry + '.fib'))]
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as directory:
                emitted = run_cli('emit-c', *args, timeout=120)
                self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
                native = self.compile_run(emitted.stdout, directory)
                hosted = run_cli('run', *args, text=False, timeout=120)
                for result in (hosted, native):
                    self.assertEqual((result.returncode, result.stdout, result.stderr), (0, expected, b''))

    def test_checked_source_binary_borrowed_slice_in_pair(self):
        args = ['--source-dir', str(EXAMPLES), str(EXAMPLES / 'Input.fib')]
        checked = run_cli('check', *args, timeout=120)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        emitted = run_cli('emit-c-binary', *args, timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        with tempfile.TemporaryDirectory() as directory:
            for supplied in (b'', b'x', b'x\0\xff', b'abc'):
                with self.subTest(supplied=supplied):
                    hosted = subprocess.run([str(ROOT / 'build/exec/fibril'), 'run-binary', *args],
                        input=supplied, capture_output=True, timeout=120)
                    native = self.compile_run(emitted.stdout, directory, binary=True, supplied=supplied)
                    for result in (hosted, native):
                        self.assertEqual((result.returncode, result.stdout, result.stderr),
                                         (0, supplied[1:3], b''))

    def test_checked_source_erased_and_unused_fields_and_dormant_branch(self):
        declarations = ('double : (x : String) -> String\ndouble x = appendString x x\n'
                        'v0 : String\nv0 = "0123456789abcdef"\n' +
                        ''.join(f'v{i} : String\nv{i} = double v{i-1}\n' for i in range(1, 22)))
        source = r'''module Main
record Lazy : Type 0 where
  constructor MkLazy
  eliminator useLazy
  0 erased : String
  unused : String
  1 kept : String
render : (1 item : Lazy) -> String
render item = useLazy (\(0 self : Lazy) => String) item
  (\(0 erased : String) => \(unused : String) => \(1 kept : String) => kept)
'''
        body = '\nmain : IO Unit\nmain = putStrLn (render (MkLazy v21 v21 (if True then "kept" else v21)))\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source + declarations + body)
            args = ['--source-dir', directory, str(path)]
            for emit, run in [('emit-c', 'run'), ('emit-c-binary', 'run-binary')]:
                if emit.endswith('binary'):
                    binary_body = body.replace('putStrLn (render', 'emitText (render')
                    helper = r'''
emitText : (1 text : String) -> IO Unit
emitText text = primUTF8Case Bytes (IO Unit) (primUTF8Encode text) primRejectBytes
  (\(1 bytes : Bytes) => primWriteBytes bytes)
'''
                    path.write_text(source + declarations + helper + binary_body)
                emitted = run_cli(emit, *args, timeout=120)
                self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
                native = self.compile_run(emitted.stdout, directory, binary=emit.endswith('binary'))
                hosted = run_cli(run, *args, text=False, timeout=120)
                expected = b'kept' if emit.endswith('binary') else b'kept\n'
                for result in (hosted, native):
                    self.assertEqual((result.returncode, result.stdout, result.stderr), (0, expected, b''))

    def test_checked_source_erased_pair_capabilities_reject_before_output(self):
        declarations = r'''module Main
record Hidden : Type 0 where
  constructor MkHidden
  eliminator useHidden
  0 action : IO Unit
  1 kept : Unit

discard : (1 item : Hidden) -> IO Unit
discard item = useHidden (\(0 self : Hidden) => IO Unit) item
  (\(0 action : IO Unit) => \(1 kept : Unit) => case kept of () => pure Unit ())
'''
        cases = [('primFlushBytes', 'putStrLn "prefix"', 'run', 'emit-c',
                  b'Binary IO requires the explicit binary runner'),
                 ('if True then pure Unit () else primFlushBytes', 'putStrLn "prefix"',
                  'run', 'emit-c', b'Binary IO requires the explicit binary runner'),
                 ('putStrLn "hidden"', 'primWriteBytes (primBytesOctetMod256 Zero)',
                  'run-binary', 'emit-c-binary', b'Native binary entry rejects non-binary IO/references')]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            args = ['--source-dir', directory, str(path)]
            for forbidden, prefix, run, emit, diagnostic in cases:
                with self.subTest(forbidden=forbidden):
                    path.write_text(declarations + '\nmain : IO Unit\nmain = do\n  ' + prefix +
                                    '\n  discard (MkHidden (' + forbidden + ') ())\n')
                    checked = run_cli('check', *args, timeout=120)
                    self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                    hosted = run_cli(run, *args, text=False, timeout=120)
                    emitted = run_cli(emit, *args, text=False, timeout=120)
                    for result in (hosted, emitted):
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(result.stdout, b'')
                    self.assertIn(diagnostic, emitted.stderr)

    def test_source_pair_quantity_misuse_is_rejected(self):
        original = (EXAMPLES / 'Pairs.fib').read_text().replace('module Pairs', 'module Main').replace('export\n', '')
        replacements = [
            ('appendString payload (appendString suffix suffix)', 'appendString erased payload'),
            ('appendString payload (appendString suffix suffix)', 'appendString payload payload'),
            ('appendString payload (appendString suffix suffix)', 'suffix'),
            ('MkMixed "unused-first" "pair" "!"', 'MkMixed "unused-first" True "!"')]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            for old, new in replacements:
                with self.subTest(replacement=new):
                    path.write_text(original.replace(old, new) + '\nmain : IO Unit\nmain = putStrLn sample\n')
                    for command in ('check', 'emit-c', 'emit-c-binary'):
                        result = run_cli(command, '--source-dir', directory, str(path), timeout=120)
                        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertIn('Module checking:', result.stderr)
                        self.assertNotIn('static FValue', result.stdout)

    def test_raw_core_all_quantity_combinations_all_modes_and_admission(self):
        with tempfile.TemporaryDirectory(prefix='fibril-pair-core-') as directory:
            work = Path(directory)
            (work / 'Fibril').symlink_to(ROOT / 'src/Fibril', target_is_directory=True)
            (work / 'Tests').symlink_to(ROOT / 'test/src/Tests', target_is_directory=True)
            (work / 'PairCompare.idr').write_text(RAW_OBSERVER)
            env = os.environ.copy()
            env.setdefault('CHEZ', shutil.which('chez') or shutil.which('scheme') or 'chez')
            env['FIBRIL_PAIR_OUTPUT'] = directory
            built = subprocess.run(shlex.split(env.get('IDRIS2', 'idris2')) +
                ['--source-dir', directory, '--build-dir', str(work / 'build'),
                 '--output-dir', str(work / 'bin'), '-o', 'pair-core', str(work / 'PairCompare.idr')],
                cwd=ROOT, env=env, capture_output=True, timeout=240)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            self.assertNotIn(b'Error:', built.stdout + built.stderr)
            self.assertNotIn(b'compiling hole', built.stdout + built.stderr)
            observed = subprocess.run([str(work / 'bin/pair-core')], cwd=work, env=env, capture_output=True, timeout=120)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertNotIn(b'FAIL:', observed.stdout)
            files = sorted(work.glob('*.c'))
            self.assertEqual(len(files), 36)
            for source in files:
                with self.subTest(fixture=source.stem):
                    _, first, second = source.stem.split('-')
                    code = source.read_text()
                    self.assertIn(f'f_pair(r, e, {int(first == "erased")}, {int(second == "erased")},', code)
                    result = self.compile_run(code, directory, binary=source.stem.startswith('binary-'), name=source.stem)
                    self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'', b''))

    def test_raw_runtime_fields_and_branches_are_lazy(self):
        with tempfile.TemporaryDirectory() as directory:
            result = self.compile_run(RAW_LAZINESS, directory)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'', b''))


if __name__ == '__main__':
    unittest.main()
