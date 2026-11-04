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
                 (['--source-dir', str(ROOT / 'examples/modules/implicit-arguments'), str(ROOT / 'examples/modules/implicit-arguments/Main.fib')], b'queued: receipt\nexplicit type\nphantom type\n'),
                 (['--package', str(ROOT / 'examples/packages/mailer/fibril.yaml')], b'accepted by relay: demo-1 (not delivery)\n')]
        for args, output in cases:
            with self.subTest(args=args), tempfile.TemporaryDirectory() as directory:
                _, native = self.compile_and_run(args, directory)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, output)

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
            'main : IO Unit\nmain = if True then putStrLn "yes" else putStrLn "no"\n',
            'main : IO Unit\nmain = do\n  putStrLn "before"\n  if True then putStrLn "yes" else putStrLn "no"\n',
            'main : IO Unit\nmain = let (0 flag : Bool) = True in putStrLn "erased"\n',
            'main : IO Unit\nmain = putStrLn False\n',
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
