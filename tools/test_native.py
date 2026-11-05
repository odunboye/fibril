#!/usr/bin/env python3
"""End-to-end tests: emit checked C, compile it, then execute it explicitly."""
from pathlib import Path
import os
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

RUNTIME = ROOT / 'runtime/native'
CC = shlex.split(os.environ.get('CC', 'cc'))


class NativeTests(unittest.TestCase):
    def compile_and_run(self, args, directory):
        emitted = run_cli('emit-c', *args, timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        c_file = Path(directory) / 'program.c'
        executable = Path(directory) / 'program'
        c_file.write_text(emitted.stdout, encoding='utf-8')
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                                      '-I', str(RUNTIME), str(c_file), str(RUNTIME / 'fibril_runtime.c'),
                                      '-o', str(executable)], capture_output=True, text=True, timeout=120)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        result = subprocess.run([str(executable)], capture_output=True, timeout=120)
        return emitted.stdout, result

    def test_core_examples_match_reference_runner(self):
        for example in ['hello-world', 'console-sequence', 'io-functions', 'do-let', 'do-result', 'string-append']:
            with self.subTest(example=example), tempfile.TemporaryDirectory() as directory:
                path = ROOT / 'examples/core' / (example + '.fib')
                _, native = self.compile_and_run([str(path)], directory)
                reference = run_cli('run', str(path), text=False, timeout=120)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(reference.returncode, 0, reference.stderr)
                self.assertEqual(native.stdout, reference.stdout)

    def test_imported_module_and_package_entry(self):
        cases = [(['--source-dir', str(ROOT / 'examples/modules/checked'), str(ROOT / 'examples/modules/checked/Main.fib')], b'Hello, Fibril!\n'),
                 (['--source-dir', str(ROOT / 'examples/modules/implicit-arguments'), str(ROOT / 'examples/modules/implicit-arguments/Main.fib')], b'queued: receipt\nexplicit type\nphantom type\nboth inferred\npartly explicit\n'),
                 (['--package', str(ROOT / 'examples/packages/mailer/fibril.yaml')], b'accepted by relay: demo-1 (not delivery)\n')]
        for args, output in cases:
            with self.subTest(args=args), tempfile.TemporaryDirectory() as directory:
                _, native = self.compile_and_run(args, directory)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, output)

    def test_native_finite_data_and_branches_match_reference(self):
        cases = [('implicit-constructors', b'receipt\n'),
                 ('direct-data-case', b'L: hello\nR: yes\nno\n')]
        for example, expected in cases:
            with self.subTest(example=example), tempfile.TemporaryDirectory() as directory:
                root = ROOT / 'examples/modules' / example
                args = ['--source-dir', str(root), str(root / 'Main.fib')]
                _, native = self.compile_and_run(args, directory)
                reference = run_cli('run', *args, text=False, timeout=120)
                self.assertEqual(reference.returncode, 0, reference.stderr)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, expected)
                self.assertEqual(native.stdout, reference.stdout)

    def test_native_nullary_unary_and_captured_environments(self):
        source = ('''module Main

data Option {0 A : Type} : Type where
  None : Option A
  Some : (1 value : A) -> Option A

make : (1 prefix : String) -> Option String
make prefix = Some (appendString prefix "payload")
render : (1 suffix : String) -> (1 value : Option String) -> String
render suffix value = case value of
  None => suffix
  Some text => appendString text suffix
main : IO Unit
main = do
  putStrLn (render " suffix" (make "captured "))
  putStrLn (render "none" (None {String}))
  putStrLn (if equalString "λ" "λ" then "equal" else "unequal")
  putStrLn (if equalString "x" "xx" then "bad" else "different")
''')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            args = ['--source-dir', directory, str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'captured payload suffix\nnone\nequal\ndifferent\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_native_data_preserves_lazy_and_erased_payloads(self):
        doubling = ('double : (x : String) -> String\ndouble x = appendString x x\n'
                    'v0 : String\nv0 = "0123456789abcdef"\n' +
                    ''.join(f'v{i} : String\nv{i} = double v{i-1}\n' for i in range(1, 22)))
        source = ('module Main\n' + doubling + '''
data Choice : Type where
  Empty : Choice
  Ignored : (value : String) -> Choice
  Erased : (0 value : String) -> Choice
render : (1 item : Choice) -> String
render item = case item of
  Empty => "empty"
  Ignored value => "ignored"
  Erased value => "erased"
main : IO Unit
main = do
  putStrLn (render (Ignored v21))
  putStrLn (render (Erased v21))
  if True then putStrLn "selected" else putStrLn v21
''')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            _, native = self.compile_and_run(['--source-dir', directory, str(path)], directory)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'ignored\nerased\nselected\n')
            path.write_text(source.replace('Ignored v21', 'Ignored "small"').replace('Erased v21', 'Erased "small"').replace('else putStrLn v21', 'else putStrLn "unselected"'))
            args = ['--source-dir', directory, str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.stdout, reference.stdout)

    def test_real_runtime_computation_erasure_and_utf8(self):
        source = ('identity : (0 A : Type) -> (1 x : A) -> A\nidentity T x = x\n'
                  'render : (1 x : String) -> String\nrender x = appendString x " \\\"quote\\\" \\\\ λ 水 🌍"\n'
                  'main : IO Unit\nmain = putStrLn (render (identity String "hello"))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'main.fib'
            path.write_text(source, encoding='utf-8')
            c, native = self.compile_and_run([str(path)], directory)
            self.assertIn('f_append(', c)
            self.assertIn('f_apply(', c)
            self.assertNotIn('hello', c)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, 'hello "quote" \\ λ 水 🌍\n'.encode())
            reference = run_cli('run', str(path), text=False)
            self.assertEqual(native.stdout, reference.stdout)

    def test_empty_output_and_escaped_control_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'main.fib'
            path.write_text('main : IO Unit\nmain = pure Unit ()\n')
            _, native = self.compile_and_run([str(path)], directory)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'')
            path.write_text('main : IO Unit\nmain = putStrLn "a\\nb\\tc\\r"\n')
            _, native = self.compile_and_run([str(path)], directory)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'a\nb\tc\r\n')
            reference = run_cli('run', str(path), text=False)
            self.assertEqual(native.stdout, reference.stdout)

    def test_unused_argument_is_lazy_and_late_failure_has_no_stdout(self):
        declarations = ('double : (x : String) -> String\ndouble x = appendString x x\n'
                        'v0 : String\nv0 = "0123456789abcdef"\n' +
                        ''.join(f'v{i} : String\nv{i} = double v{i-1}\n' for i in range(1, 22)))
        unused = declarations + ('ignore : (x : String) -> String\nignore x = "ok"\n'
                                 'main : IO Unit\nmain = putStrLn (ignore v21)\n')
        late = declarations + 'main : IO Unit\nmain = do\n  putStrLn "before"\n  putStrLn v21\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'main.fib'
            path.write_text(unused)
            _, native = self.compile_and_run([str(path)], directory)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'ok\n')
            path.write_text(late)
            _, native = self.compile_and_run([str(path)], directory)
            self.assertNotEqual(native.returncode, 0)
            self.assertEqual(native.stdout, b'')
            self.assertIn(b'allocation budget', native.stderr)

    def test_output_action_limit_is_checked_before_any_write(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'main.fib'
            for extra, expected in [(False, 64), (True, 0)]:
                source = ('block : IO Unit\nblock = do\n' + '  putStrLn "x"\n' * 32 +
                          'main : IO Unit\nmain = do\n  block\n  block\n' +
                          ('  putStrLn "x"\n' if extra else ''))
                path.write_text(source)
                _, native = self.compile_and_run([str(path)], directory)
                self.assertEqual(len(native.stdout.splitlines()), expected)
                if expected:
                    self.assertEqual(native.returncode, 0, native.stderr)
                else:
                    self.assertNotEqual(native.returncode, 0)
                    self.assertIn(b'action budget', native.stderr)

    def test_nat_recursion_is_not_yet_native(self):
        root = ROOT / 'examples/modules/nat-recursion'
        emitted = run_cli('emit-c', '--source-dir', str(root), str(root / 'Main.fib'), timeout=120)
        self.assertNotEqual(emitted.returncode, 0)
        self.assertEqual(emitted.stdout, '')
        self.assertIn('does not support this computational core construct', emitted.stderr)
        for example in ['nat-predecessor', 'recursive-equations', 'recursive-render']:
            root = ROOT / 'examples/modules' / example
            emitted = run_cli('emit-c', '--source-dir', str(root), str(root / 'Main.fib'), timeout=120)
            self.assertNotEqual(emitted.returncode, 0)
            self.assertEqual(emitted.stdout, '')
            self.assertIn('does not support this computational core construct', emitted.stderr)

    def test_recursive_data_is_not_yet_native(self):
        for example in ['recursive-data', 'recursive-list']:
            root = ROOT / 'examples/modules' / example
            emitted = run_cli('emit-c', '--source-dir', str(root), str(root / 'Main.fib'), timeout=120)
            self.assertNotEqual(emitted.returncode, 0)
            self.assertEqual(emitted.stdout, '')
            self.assertIn('does not support this computational core construct', emitted.stderr)

    def test_wider_data_still_fails_closed_without_pair_lowering(self):
        root = ROOT / 'examples/modules/data'
        args = ['--source-dir', str(root), str(root / 'Main.fib')]
        reference = run_cli('run', *args, timeout=120)
        self.assertEqual(reference.returncode, 0, reference.stdout + reference.stderr)
        emitted = run_cli('emit-c', *args, timeout=120)
        self.assertNotEqual(emitted.returncode, 0)
        self.assertEqual(emitted.stdout, '')
        self.assertIn('does not support this computational core construct', emitted.stderr)

    def test_invalid_import_is_rejected_before_c_emission(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Bad.fib').write_text('module Bad\nexport\nbroken : String\nbroken = True\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport Bad\nmain : IO Unit\nmain = putStrLn "never"\n')
            result = run_cli('emit-c', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertTrue(result.stderr)

    def test_rejection_never_emits_partial_c(self):
        programs = [
            '0 hidden : String\nhidden = "secret"\nmain : IO Unit\nmain = putStrLn hidden\n',
            'main : Bool\nmain = True\n',
            'main : IO Unit\nmain = putStrLn False\n',
            'bad : (1 x : String) -> (1 b : Bool) -> String\nbad x b = if b then x else "lost"\nmain : IO Unit\nmain = putStrLn (bad "x" True)\n',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'main.fib'
            for source in programs:
                with self.subTest(source=source):
                    path.write_text(source)
                    result = run_cli('emit-c', str(path), timeout=120)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, '')
                    self.assertTrue(result.stderr)


if __name__ == '__main__':
    unittest.main()
