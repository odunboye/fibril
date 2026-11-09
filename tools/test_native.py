#!/usr/bin/env python3
"""End-to-end tests: emit checked C, compile it, then execute it explicitly."""
from pathlib import Path
import os
import shutil
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
        for example in ['hello-world', 'console-sequence', 'io-functions', 'do-let', 'do-result', 'string-append', 'bytes-equal']:
            with self.subTest(example=example), tempfile.TemporaryDirectory() as directory:
                path = ROOT / 'examples/core' / (example + '.fib')
                _, native = self.compile_and_run([str(path)], directory)
                reference = run_cli('run', str(path), text=False, timeout=120)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(reference.returncode, 0, reference.stderr)
                self.assertEqual(native.stdout, reference.stdout)

    def test_nat_case_and_clauses_match_reference(self):
        for definition in ('f Zero = Zero\nf Succ n = Succ n',
                           'f Zero = Zero\nf item = item',
                           'f n = case n of\n  Zero => Zero\n  Succ k => Succ k'):
            for value, expected in (('Zero', b'\n'), ('Succ (Succ Zero)', b'!!\n')):
                with self.subTest(definition=definition, value=value), tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / 'Main.fib'
                    path.write_text('module Main\nf : Nat -> Nat\n' + definition +
                        '\nmarks : (1 n : Nat) -> String\nmarks n = natRec '
                        '(\\(0 k : Nat) => String) "" '
                        '(\\(0 k : Nat) => \\(1 result : String) => appendString result "!") n\n'
                        + f'main : IO Unit\nmain = putStrLn (marks (f ({value})))\n')
                    args = ['--source-dir', directory, str(path)]
                    _, native = self.compile_and_run(args, directory)
                    reference = run_cli('run', *args, text=False, timeout=120)
                    self.assertEqual(reference.returncode, 0, reference.stderr)
                    self.assertEqual(native.returncode, 0, native.stderr)
                    self.assertEqual(native.stdout, expected)
                    self.assertEqual(native.stdout, reference.stdout)

    def test_imported_module_and_package_entry(self):
        cases = [(['--source-dir', str(ROOT / 'examples/modules/nested-data'), str(ROOT / 'examples/modules/nested-data/Main.fib')], b'!!!\n'),
                 (['--source-dir', str(ROOT / 'examples/modules/mutual-data'), str(ROOT / 'examples/modules/mutual-data/Main.fib')], b'..0\n'),
                 (['--source-dir', str(ROOT / 'examples/modules/index-refinement'), str(ROOT / 'examples/modules/index-refinement/Main.fib')], b'first\nsecond\n'),
                 (['--source-dir', str(ROOT / 'examples/modules/indexed-vect'), str(ROOT / 'examples/modules/indexed-vect/Main.fib')], b'first\n!!!!\n'),
                 (['--source-dir', str(ROOT / 'examples/modules/checked'), str(ROOT / 'examples/modules/checked/Main.fib')], b'Hello, Fibril!\n'),
                 (['--source-dir', str(ROOT / 'examples/modules/implicit-arguments'), str(ROOT / 'examples/modules/implicit-arguments/Main.fib')], b'queued: receipt\nexplicit type\nphantom type\nboth inferred\npartly explicit\n'),
                 (['--package', str(ROOT / 'examples/packages/mailer/fibril.yaml')], b'accepted by relay: demo-1 (not delivery)\n')]
        for args, output in cases:
            with self.subTest(args=args), tempfile.TemporaryDirectory() as directory:
                _, native = self.compile_and_run(args, directory)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, output)

    def test_general_recursion_fix_matches_reference(self):
        # A size-change-admitted Fix is emitted as a recursive native closure. Outputs must
        # agree with the hosted evaluator; the fuel only widens the hosted planning budget.
        root = ROOT / 'examples/modules/general-recursion'
        expected = {'Half': b'!!!\n', 'Chain': b'xxx\n', 'Swap': b'!\n', 'Doubling': b'!!!!\n',
                    'Fibonacci': b'!!!\n', 'Ackermann': b'!!!\n',
                    'MutualChain': b'zero links: even\ntwo links: even\nthree links: odd\n',
                    'MutualRing': b'.\nrgbrg.\nbr.\n',
                    'MutualForward': b'.\nststst.\n'}
        for name, output in expected.items():
            with self.subTest(program=name), tempfile.TemporaryDirectory() as directory:
                args = ['--source-dir', str(root), str(root / (name + '.fib'))]
                _, native = self.compile_and_run(args, directory)
                reference = run_cli('run', '--source-dir', str(root), '--fuel', '4096',
                                    str(root / (name + '.fib')), text=False, timeout=120)
                self.assertEqual(reference.returncode, 0, reference.stderr)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, output)
                self.assertEqual(native.stdout, reference.stdout)

    def test_general_recursive_data_matches_reference(self):
        # General recursive families lower to native variants whose payload is a nest of pairs.
        # Native output must agree with the hosted evaluator for the shipped example and for
        # constructors with zero, one, two and four fields (linear and unrestricted).
        example = ROOT / 'examples/modules/general-data'
        wide = ('module Main\n\ndata Wide : Type where\n  Unit0 : Wide\n  One : (a : String) -> Wide\n'
                '  Two : (a : String) -> (rest : Wide) -> Wide\n'
                '  Four : (a : String) -> (b : String) -> (left : Wide) -> (right : Wide) -> Wide\n\n'
                'show : (w : Wide) -> String\nshow w = case w of\n  Unit0 => "u"\n  One a => a\n'
                '  Two a rest => appendString a (show rest)\n'
                '  Four a b left right => appendString a (appendString b (appendString (show left) (show right)))\n\n'
                'main : IO Unit\nmain = putStrLn (show (Four "a" "b" (Two "c" (One "d")) (Four "e" "f" Unit0 (One "g"))))\n')
        cases = [('shipped example', ['--source-dir', str(example), str(example / 'Main.fib')], b'...\n(b(bb))\n')]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(wide)
            cases.append(('wide constructors', ['--source-dir', directory, str(path)], b'abcdefug\n'))
            for label, args, output in cases:
                with self.subTest(program=label), tempfile.TemporaryDirectory() as build:
                    _, native = self.compile_and_run(args, build)
                    reference = run_cli('run', *args[:-1], '--fuel', '4096', args[-1], text=False, timeout=120)
                    self.assertEqual(reference.returncode, 0, reference.stderr)
                    self.assertEqual(native.returncode, 0, native.stderr)
                    self.assertEqual(native.stdout, output)
                    self.assertEqual(native.stdout, reference.stdout)

    def test_fix_native_budget_is_the_fixed_runtime_limit(self):
        # Native Fix inherits the runtime's fixed evaluation budget; it does not widen it.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def nest(depth):
                text = '(Succ Zero)'
                for _ in range(depth):
                    text = '(double ' + text + ')'
                return text
            source = ('module Main\n'
                      'double : (1 n : Nat) -> Nat\n'
                      'double n = natRec (\\(0 k : Nat) => Nat) Zero (\\(0 k : Nat) => \\(1 r : Nat) => Succ (Succ r)) n\n'
                      'half : (1 n : Nat) -> Nat\nhalf n = case n of\n  Zero => Zero\n'
                      '  Succ a => case a of\n    Zero => Zero\n    Succ b => Succ (half b)\n'
                      'marks : (1 count : Nat) -> String\n'
                      'marks count = natRec (\\(0 k : Nat) => String) ""\n'
                      '  (\\(0 k : Nat) => \\(1 result : String) => appendString result "!") count\n'
                      'main : IO Unit\nmain = putStrLn (marks (half ' + nest(7) + '))\n')
            (root / 'Main.fib').write_text(source)
            _, native = self.compile_and_run(['--source-dir', str(root), str(root / 'Main.fib')], directory)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'!' * 64 + b'\n')
            (root / 'Main.fib').write_text(source.replace(nest(7), nest(9)))
            _, native = self.compile_and_run(['--source-dir', str(root), str(root / 'Main.fib')], directory)
            self.assertNotEqual(native.returncode, 0)
            self.assertIn(b'native evaluation budget exhausted', native.stderr)

    def test_mutual_nat_parity_matches_reference(self):
        root = ROOT / 'examples/modules/mutual-parity'
        args = ['--source-dir', str(root), str(root / 'Main.fib')]
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'even zero\nodd one\neven two\nodd three\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_mutual_nat_payload_matches_reference(self):
        root = ROOT / 'examples/modules/mutual-parity'
        args = ['--source-dir', str(root), str(root / 'Payload.fib')]
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'identity\nnegated\nidentity again\nother entry\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_mutual_nat_forwarding_alias_matches_reference(self):
        root = ROOT / 'examples/modules/mutual-parity'
        args = ['--source-dir', str(root), str(root / 'Reordered.fib')]
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'forwarded\nreordered\nunchanged payload\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_linear_accumulator_fold_matches_reference(self):
        root = ROOT / 'examples/modules/linear-accumulator'
        args = ['--source-dir', str(root), str(root / 'Main.fib')]
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'bac\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_linear_accumulator_computed_update_matches_reference(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        with tempfile.TemporaryDirectory() as directory:
            args = ['--source-dir', str(fixture), str(fixture / 'Decorated.fib')]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'b!a!c\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_distinct_string_accumulator_matches_reference(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        args = ['--source-dir', str(fixture), str(fixture / 'StringAccumulator.fib')]
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'cab\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_accumulator_computed_base_matches_reference(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        args = ['--source-dir', str(fixture), str(fixture / 'Matches.fib')]
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'matched\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_accumulator_partial_application_matches_reference(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = (fixture / 'Matches.fib').read_text()
        prefix = source[:source.index('main : IO Unit')]
        source = prefix + ('''main : IO Unit
main = let (1 remaining : (1 acc : String) -> Bool) =
  matchesOnto (Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))) in
  if remaining "c" then putStrLn "matched" else putStrLn "different"
''')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Matches.fib'
            path.write_text(source)
            args = ['--source-dir', str(root), str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'matched\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_accumulator_first_and_partial_application_match_reference(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        path = fixture / 'AccumulatorFirst.fib'
        with tempfile.TemporaryDirectory() as directory:
            args = ['--source-dir', str(fixture), str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'matched\n')
            self.assertEqual(native.stdout, reference.stdout)
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            partial = root / 'AccumulatorFirst.fib'
            source = path.read_text()
            prefix = source[:source.index('main : IO Unit')]
            partial.write_text(prefix + ('''main : IO Unit
main = let (1 remaining : (1 items : Data.Items.Items String) -> Bool) = matchesFrom "c" in
  if remaining (Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String})))
  then putStrLn "matched" else putStrLn "different"
'''))
            args = ['--source-dir', str(root), str(partial)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'matched\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_uniform_prefix_accumulators_match_reference(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        for filename, expected in [('UniformPrefix.fib', b'b!a!c\n'),
                                   ('UniformPrefixFirst.fib', b'ca!b!?\n')]:
            with self.subTest(filename=filename), tempfile.TemporaryDirectory() as directory:
                args = ['--source-dir', str(fixture), str(fixture / filename)]
                _, native = self.compile_and_run(args, directory)
                reference = run_cli('run', *args, text=False, timeout=120)
                self.assertEqual(reference.returncode, 0, reference.stderr)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, expected)
                self.assertEqual(native.stdout, reference.stdout)

    def test_uniform_prefix_accumulator_partial_application(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = (fixture / 'UniformPrefixFirst.fib').read_text()
        prefix = source[:source.index('main : IO Unit')]
        source = prefix + ('''main : IO Unit
main = let (1 remaining : (1 items : Data.Items.Items String) -> String) =
  appendMappedFrom {String} mark "?" "c" in
  putStrLn (remaining (Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))))
''')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'UniformPrefixFirst.fib'
            path.write_text(source)
            args = ['--source-dir', str(root), str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'ca!b!?\n')
            self.assertEqual(native.stdout, reference.stdout)

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

    def test_checked_recursive_examples_match_reference(self):
        examples = [('nat-recursion', b'receipt!!!\n'), ('nat-predecessor', b'!!!\n'),
                    ('recursive-equations', b'!!!!\n'), ('recursive-render', b'receipt!!\n'),
                    ('recursive-data', b'!!\n'), ('recursive-list', b'hello world\n'),
                    ('polymorphic-recursion', b'hello world\n'), ('polymorphic-map', b'hello! world!\n'),
                    ('uniform-recursion', b'yes,no,\n'), ('uniform-nat-chain', b'receipt!!\n~~\n'),
                    ('conditional-recursion', b'TT\nFF\nTT\nFF\na!b!\na?b?\n')]
        for example, expected in examples:
            with self.subTest(example=example), tempfile.TemporaryDirectory() as directory:
                root = ROOT / 'examples/modules' / example
                args = ['--source-dir', str(root), str(root / 'Main.fib')]
                _, native = self.compile_and_run(args, directory)
                reference = run_cli('run', *args, text=False, timeout=120)
                self.assertEqual(reference.returncode, 0, reference.stderr)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, expected)
                self.assertEqual(native.stdout, reference.stdout)

    def test_polymorphic_mapping_with_distinct_element_types(self):
        source = (ROOT / 'examples/modules/polymorphic-map/Main.fib').read_text()
        source = source.replace('exclaim : (1 text : String) -> String\nexclaim text = appendString text "!"',
                                'exclaim : (1 flag : Bool) -> String\nexclaim flag = if flag then "T" else "F"')
        source = source.replace('mapItems {String} {String} exclaim', 'mapItems {Bool} {String} exclaim')
        source = source.replace('Prepend "hello" (Prepend " world" (Empty {String}))', 'Prepend True (Prepend False (Empty {Bool}))')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            args = ['--source-dir', directory, str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'TF\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_recursive_cases_and_captured_fold_environment(self):
        source = r'''module Main

data Chain : Type where
  eliminator foldChain
  Empty : Chain
  More : (1 tail : Chain) -> Chain

data Items {0 A : Type} : Type where
  eliminator foldItems
  Nil : Items A
  Cons : (1 head : A) -> (1 tail : Items A) -> Items A

marks : (1 prefix : String) -> (1 xs : Chain) -> String
marks prefix xs = case xs of
  Empty => prefix
  More tail => foldChain (\(0 self : Chain) => String) prefix
    (\(0 rest : Chain) => \(1 result : String) => appendString result "!") tail

join : (1 xs : Items String) -> String
join xs = case xs of
  Nil => "empty"
  Cons head tail => appendString head (foldItems String (\(0 self : Items String) => String) "!"
    (\(1 item : String) => \(0 rest : Items String) => \(1 result : String) => appendString item result) tail)

main : IO Unit
main = do
  putStrLn (marks "base" Empty)
  putStrLn (marks "base" (More (More Empty)))
  putStrLn (join (Nil {String}))
  putStrLn (join (Cons "a" (Cons "b" (Nil {String}))))
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            args = ['--source-dir', directory, str(path)]
            _, native = self.compile_and_run(args, directory)
            reference = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'base\nbase!\nempty\nab!\n')
            self.assertEqual(native.stdout, reference.stdout)

    def test_recursive_unselected_branch_is_lazy(self):
        doubling = ('double : (x : String) -> String\ndouble x = appendString x x\n'
                    'v0 : String\nv0 = "0123456789abcdef"\n' +
                    ''.join(f'v{i} : String\nv{i} = double v{i-1}\n' for i in range(1, 22)))
        import textwrap
        source = 'module Main\n' + doubling + textwrap.dedent(r'''
        data Items {0 A : Type} : Type where
          eliminator foldItems
          Nil : Items A
          Cons : (1 head : A) -> (1 tail : Items A) -> Items A
        render : (1 xs : Items String) -> String
        render xs = case xs of
          Nil => v21
          Cons head tail => appendString head (foldItems String (\(0 self : Items String) => String) "!"
            (\(1 item : String) => \(0 rest : Items String) => \(1 result : String) => appendString item result) tail)
        main : IO Unit
        main = putStrLn (render (Cons "selected" (Nil {String})))
        ''')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            _, native = self.compile_and_run(['--source-dir', directory, str(path)], directory)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'selected!\n')

    def test_runtime_nat_case_reuses_predecessor_thunk(self):
        # Core unrestricted branches are not yet expressible as source patterns.
        source = r'''
#include "fibril_runtime.h"
static int calls;
static FValue *zero(FRuntime *r, FEnv *e) { (void)e; calls++; return f_nat_zero(r); }
static FValue *value(FRuntime *r, FEnv *e) { return f_nat_succ(r, e, zero); }
static FValue *var(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *text(FRuntime *r, FEnv *e) { (void)e; return f_literal(r, (const unsigned char *)"x", 1); }
static FValue *unused(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, text); }
static FValue *inspect(FRuntime *r, FEnv *e) { return f_nat_case(r, e, var, text, unused); }
static FValue *twice(FRuntime *r, FEnv *e) { return f_append(r, e, inspect, inspect); }
static FValue *branch(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, twice); }
static FValue *result(FRuntime *r, FEnv *e) { return f_nat_case(r, e, value, text, branch); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, result); }
int main(void) { int result = fibril_native_run(entry); return result ? result : calls == 1 ? 0 : 2; }
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'probe.c'
            executable = Path(directory) / 'probe'
            path.write_text(source)
            build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                                          '-I', str(RUNTIME), str(path), str(RUNTIME / 'fibril_runtime.c'),
                                          '-o', str(executable)], capture_output=True, text=True, timeout=120)
            self.assertEqual(build.returncode, 0, build.stderr)
            native = subprocess.run([str(executable)], capture_output=True, timeout=120)
            self.assertEqual(native.returncode, 0, native.stderr)
            self.assertEqual(native.stdout, b'xx\n')

    def test_runtime_fold_thunks_are_lazy_and_memoized(self):
        # Direct runtime probes intentionally bypass the Fibril checker. They
        # exercise delayed and shared thunks, not source-level typing claims.
        probes = [r'''
#include "fibril_runtime.h"
static FValue *bomb(FRuntime *r, FEnv *e) { (void)e; return f_variable(r, NULL, 0); }
static FValue *value(FRuntime *r, FEnv *e) { return f_nat_succ(r, e, bomb); }
static FValue *literal(FRuntime *r, FEnv *e) { (void)e; return f_literal(r, (const unsigned char *)"lazy", 4); }
static FValue *inner(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, literal); }
static FValue *step(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, inner); }
static FValue *fold(FRuntime *r, FEnv *e) { return f_nat_rec(r, e, bomb, step, value); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, fold); }
int main(void) { return fibril_native_run(entry); }
''', r'''
#include "fibril_runtime.h"
static int calls;
static FValue *zero(FRuntime *r, FEnv *e) { (void)e; return f_nat_zero(r); }
static FValue *value(FRuntime *r, FEnv *e) { return f_nat_succ(r, e, zero); }
static FValue *base(FRuntime *r, FEnv *e) { (void)e; calls++; return f_literal(r, (const unsigned char *)"x", 1); }
static FValue *var(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *twice(FRuntime *r, FEnv *e) { return f_append(r, e, var, var); }
static FValue *inner(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, twice); }
static FValue *step(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, inner); }
static FValue *fold(FRuntime *r, FEnv *e) { return f_nat_rec(r, e, base, step, value); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, fold); }
int main(void) { int result = fibril_native_run(entry); return result ? result : calls == 1 ? 0 : 2; }
''']
        for source, expected in zip(probes, [b'lazy\n', b'xx\n']):
            with self.subTest(expected=expected), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'probe.c'
                executable = Path(directory) / 'probe'
                path.write_text(source)
                build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                                              '-I', str(RUNTIME), str(path), str(RUNTIME / 'fibril_runtime.c'),
                                              '-o', str(executable)], capture_output=True, text=True, timeout=120)
                self.assertEqual(build.returncode, 0, build.stderr)
                native = subprocess.run([str(executable)], capture_output=True, timeout=120)
                self.assertEqual(native.returncode, 0, native.stderr)
                self.assertEqual(native.stdout, expected)

    def test_runtime_recursive_tags_and_erased_slots_fail_closed(self):
        # These deliberately malformed runtime calls are not checked Fibril.
        probes = [r'''
#include "fibril_runtime.h"
static FValue *zero(FRuntime *r, FEnv *e) { (void)e; return f_nat_zero(r); }
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *fold(FRuntime *r, FEnv *e) { return f_rec_fold(r, e, unit, unit, zero); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, fold); }
int main(void) { return fibril_native_run(entry); }
''', r'''
#include "fibril_runtime.h"
static FValue *zero(FRuntime *r, FEnv *e) { (void)e; return f_nat_zero(r); }
static FValue *value(FRuntime *r, FEnv *e) { return f_nat_succ(r, e, zero); }
static FValue *force_erased(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *step(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, force_erased); }
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *fold(FRuntime *r, FEnv *e) { return f_nat_rec(r, e, unit, step, value); }
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, fold); }
int main(void) { return fibril_native_run(entry); }
''']
        for source, message in zip(probes, [b'matching recursive value', b'erased argument was forced']):
            with self.subTest(message=message), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'probe.c'
                executable = Path(directory) / 'probe'
                path.write_text(source)
                build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                                              '-I', str(RUNTIME), str(path), str(RUNTIME / 'fibril_runtime.c'),
                                              '-o', str(executable)], capture_output=True, text=True, timeout=120)
                self.assertEqual(build.returncode, 0, build.stderr)
                native = subprocess.run([str(executable)], capture_output=True, timeout=120)
                self.assertNotEqual(native.returncode, 0)
                self.assertEqual(native.stdout, b'')
                self.assertIn(message, native.stderr)

    def test_recursive_budget_failure_precedes_all_output(self):
        source = ('module Main\ndouble : (1 n : Nat) -> Nat\ndouble n = case n of\n'
                  '  Zero => Zero\n  Succ k => Succ (Succ (double k))\n'
                  'n0 : Nat\nn0 = Succ Zero\n' +
                  ''.join(f'n{i} : Nat\nn{i} = double n{i-1}\n' for i in range(1, 9)) +
                  'repeat : (1 count : Nat) -> String\n'
                  'repeat count = natRec (\\(0 k : Nat) => String) "x" '
                  '(\\(0 k : Nat) => \\(1 result : String) => appendString result "!") count\n'
                  'main : IO Unit\nmain = do\n  putStrLn "must not appear"\n  putStrLn (repeat n8)\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            _, native = self.compile_and_run(['--source-dir', directory, str(path)], directory)
            self.assertNotEqual(native.returncode, 0)
            self.assertEqual(native.stdout, b'')
            self.assertIn(b'evaluation budget exhausted', native.stderr)

    def test_wider_data_pair_payload_matches_reference(self):
        root = ROOT / 'examples/modules/data'
        args = ['--source-dir', str(root), str(root / 'Main.fib')]
        reference = run_cli('run', *args, text=False, timeout=120)
        self.assertEqual(reference.returncode, 0, reference.stdout + reference.stderr)
        with tempfile.TemporaryDirectory() as directory:
            code, native = self.compile_and_run(args, directory)
            self.assertIn('f_pair(', code)
            self.assertIn('f_pair_case(', code)
            self.assertEqual((native.returncode, native.stdout, native.stderr),
                             (0, b'present\nmissing\ndependent package\n', b''))
            self.assertEqual(native.stdout, reference.stdout)

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
