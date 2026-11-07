#!/usr/bin/env python3
"""Source-level shared-global scale, visibility, execution and native admission."""
from pathlib import Path
import os
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

CC = shlex.split(os.environ.get('CC', 'cc'))
RUNTIME = ROOT / 'runtime/native'


class SharedGlobalTests(unittest.TestCase):
    def native(self, args, directory):
        emitted = run_cli('emit-c', *args, timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        source = Path(directory) / 'program.c'
        target = Path(directory) / 'program'
        source.write_text(emitted.stdout)
        built = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
            '-I', str(RUNTIME), str(source), str(RUNTIME / 'fibril_runtime.c'), '-o', str(target)],
            capture_output=True, timeout=120)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        result = subprocess.run([str(target)], capture_output=True, timeout=30)
        return emitted.stdout, result

    def test_repeated_reference_chain_stays_small_and_runs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            declarations = ['module Main', 'g0 : String', 'g0 = "shared"']
            for index in range(1, 33):
                declarations += [f'g{index} : String',
                    f'g{index} = if True then g{index - 1} else g{index - 1}']
            declarations += ['main : IO Unit', 'main = putStrLn g32']
            path = root / 'Main.fib'
            path.write_text('\n'.join(declarations) + '\n')
            args = ['--source-dir', directory, str(path)]
            checked = run_cli('check', *args, timeout=120)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            hosted = run_cli('run', *args, timeout=120)
            self.assertEqual((hosted.returncode, hosted.stdout), (0, 'shared\n'), hosted.stderr)
            code, result = self.native(args, directory)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'shared\n', b''))
            # A whole binary tree with 32 levels cannot fit this code-size bound.
            self.assertLess(len(code), 100_000)
            self.assertIn('f_global(r, fibril_global_', code)

    def test_imported_aliases_share_canonical_declaration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Library.fib').write_text('module Library\nexport\ngreeting : String\ngreeting = "imported"\n')
            path = root / 'Main.fib'
            path.write_text('module Main\nimport Library\n'
                'choose : Bool -> String\nchoose flag = if flag then Library.greeting else greeting\n'
                'main : IO Unit\nmain = putStrLn (choose True)\n')
            args = ['--source-dir', directory, str(path)]
            hosted = run_cli('run', *args, timeout=120)
            self.assertEqual((hosted.returncode, hosted.stdout), (0, 'imported\n'), hosted.stderr)
            code, result = self.native(args, directory)
            self.assertEqual((result.returncode, result.stdout), (0, b'imported\n'), result.stderr)
            # The literal is emitted once despite qualified and short aliases.
            self.assertEqual(code.count('{105,109,112,111,114,116,101,100}'), 1)

    def test_erased_global_cannot_be_used_at_runtime(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\n0 secret : String\nsecret = "hidden"\n'
                'main : IO Unit\nmain = putStrLn secret\n')
            result = run_cli('check', '--source-dir', directory, str(path), timeout=120)
            self.assertNotEqual(result.returncode, 0)

    def test_invalid_unused_private_definition_still_rejects(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\nbad : String\nbad = True\n'
                'main : IO Unit\nmain = putStrLn "unreachable"\n')
            result = run_cli('run', '--source-dir', directory, str(path), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')

    def test_erased_alias_still_supports_conversion(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\n0 Text : Type\nText = String\n'
                'greeting : Text\ngreeting = "alias"\n'
                'main : IO Unit\nmain = putStrLn greeting\n')
            result = run_cli('run', '--source-dir', directory, str(path), timeout=120)
            self.assertEqual((result.returncode, result.stdout), (0, 'alias\n'), result.stderr)

    def test_dead_binary_dependency_still_rejects_text_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\nhidden : IO Unit\nhidden = primFlushBytes\n'
                'main : IO Unit\nmain = if True then putStrLn "text" else hidden\n')
            args = ['--source-dir', directory, str(path)]
            checked = run_cli('check', *args, timeout=120)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            for command in ('run', 'emit-c'):
                with self.subTest(command=command):
                    result = run_cli(command, *args, timeout=120)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, '')

    def test_unreferenced_binary_declaration_does_not_grant_or_require_capability(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\nhidden : IO Unit\nhidden = primFlushBytes\n'
                'main : IO Unit\nmain = putStrLn "text"\n')
            args = ['--source-dir', directory, str(path)]
            result = run_cli('run', *args, timeout=120)
            self.assertEqual((result.returncode, result.stdout), (0, 'text\n'), result.stderr)
            _, native = self.native(args, directory)
            self.assertEqual((native.returncode, native.stdout), (0, b'text\n'), native.stderr)

    def test_native_payload_budget_charges_all_reachable_declarations(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\na : String\na = "' + 'a' * 5000 +
                '"\nb : String\nb = "' + 'b' * 5000 +
                '"\nmain : IO Unit\nmain = putStrLn (appendString a b)\n')
            result = run_cli('emit-c', '--source-dir', directory, str(path), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('literal admission', result.stderr)

    def test_full_email_state_model_runs_hosted_and_native(self):
        root = ROOT / 'examples/modules/email-service-full'
        args = ['--source-dir', str(root), str(root / 'Main.fib')]
        expected = b'sending\ndeferred\nqueued\nfailed\ndelivered\nbounced\nsubmission unknown\ntransition rejected\n'
        result = run_cli('run', *args, text=False, timeout=120)
        self.assertEqual((result.returncode, result.stdout), (0, expected), result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            _, native = self.native(args, directory)
            self.assertEqual((native.returncode, native.stdout), (0, expected), native.stderr)

    def test_checked_environment_constructors_are_private(self):
        compiler = shlex.split(os.environ.get('IDRIS2', 'idris2'))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Fibril').symlink_to(ROOT / 'src/Fibril', target_is_directory=True)
            # Verify the public types and safe constructors are available first;
            # a stale/missing module must not make the forgery checks pass.
            control = root / 'ContextUse.idr'
            control.write_text('module ContextUse\nimport Fibril.Core.Erased\nimport Fibril.Core.Runtime\n'
                'erased : GlobalContext\nerased = emptyGlobals\n'
                'runtime : RuntimeGlobals\nruntime = emptyRuntimeGlobals\n')
            accepted = subprocess.run(compiler + ['--source-dir', directory,
                '--build-dir', str(root / 'build'), '--check', str(control)],
                cwd=ROOT, capture_output=True, text=True, timeout=120)
            self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
            self.assertNotIn('compiling hole', accepted.stdout + accepted.stderr)
            for module, imported, typ, constructor, argument in (
                ('ForgeErased', 'Erased', 'GlobalContext', 'CheckedGlobalContext', '[]'),
                ('ForgeRuntime', 'Runtime', 'RuntimeGlobals', 'CheckedRuntimeGlobals', 'emptyGlobals'),
            ):
                with self.subTest(environment=typ):
                    path = root / (module + '.idr')
                    path.write_text(f'module {module}\nimport Fibril.Core.Erased\n'
                        f'import Fibril.Core.{imported}\nforged : {typ}\n'
                        f'forged = {constructor} {argument}\n')
                    result = subprocess.run(compiler + ['--source-dir', directory,
                        '--build-dir', str(root / 'build'), '--check', str(path)],
                        cwd=ROOT, capture_output=True, text=True, timeout=120)
                    self.assertNotEqual(result.returncode, 0)
                    diagnostic = result.stdout + result.stderr
                    self.assertIn(constructor, diagnostic)
                    self.assertTrue('private' in diagnostic or 'Undefined name' in diagnostic, diagnostic)

    def test_native_node_budget_charges_all_reachable_bodies(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            source = ['module Main',
                'marks : (1 n : Nat) -> String',
                'marks n = natRec (\\(0 k : Nat) => String) "" (\\(0 k : Nat) => \\(1 result : String) => appendString result "!") n']
            for index in range(48):
                source += [f'n{index} : Nat', f'n{index} = 200']
            source += ['main : IO Unit', 'main = do']
            source += [f'  putStrLn (marks n{index})' for index in range(48)]
            path.write_text('\n'.join(source) + '\n')
            args = ['--source-dir', directory, str(path)]
            checked = run_cli('check', *args, timeout=120)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            result = run_cli('emit-c', *args, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('core admission', result.stderr)

    def test_native_global_entry_cannot_bypass_runtime_depth_budget(self):
        # Trusted C probe, not source admission evidence: source global cycles
        # are rejected before emission. Exercise the runtime boundary directly.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'depth.c'
            target = root / 'depth'
            source.write_text('#include "fibril_runtime.h"\n'
                'static FValue *loop(FRuntime *r, FEnv *e) { (void)e; return f_global(r, loop); }\n'
                'int main(void) { return fibril_native_run(loop); }\n')
            built = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                '-I', str(RUNTIME), str(source), str(RUNTIME / 'fibril_runtime.c'), '-o', str(target)],
                capture_output=True, timeout=120)
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            result = subprocess.run([str(target)], capture_output=True, timeout=30)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')
            self.assertIn(b'native evaluation budget exhausted', result.stderr)

    def test_global_forced_inside_region_remains_valid_after_region_exit(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\ngreeting : String\ngreeting = appendString "global" "!"\n'
                'twice : String -> IO Unit\ntwice text = do\n'
                '  putStrLn (primWithRegion String (\\(0 region : Type) => text))\n'
                '  putStrLn text\n'
                'main : IO Unit\nmain = twice greeting\n')
            args = ['--source-dir', directory, str(path)]
            result = run_cli('run', *args, timeout=120)
            self.assertEqual((result.returncode, result.stdout), (0, 'global!\nglobal!\n'), result.stderr)
            _, native = self.native(args, directory)
            self.assertEqual((native.returncode, native.stdout, native.stderr),
                (0, b'global!\nglobal!\n', b''))


if __name__ == '__main__':
    unittest.main()
