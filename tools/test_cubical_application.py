#!/usr/bin/env python3
"""Ordinary .fib constant-path guards: one shared gate, erased before execution."""
from pathlib import Path
import json
import os
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

EXAMPLE = ROOT / 'examples/cubical/policy-guard.fib'
SOURCE = EXAMPLE.read_text()
GUARD = 'cubical policyStable : allow = reviewed by refl\n'
REQUIRES = 'requires policyStable\n'
BOOL_EXAMPLE = ROOT / 'examples/cubical/bool-refactoring.fib'
BOOL_SOURCE = BOOL_EXAMPLE.read_text()
BOOL_GUARD = GUARD.replace('by refl', 'by boolCases')
RUNTIME = ROOT / 'runtime/native'
CC = shlex.split(os.environ.get('CC', 'cc'))


class CubicalApplicationTests(unittest.TestCase):
    def assert_rejected(self, source, diagnostic=None, commands=(('check',),)):
        with tempfile.TemporaryDirectory(prefix='fibril-path-guard-') as directory:
            path = Path(directory) / 'program.fib'
            path.write_text(source)
            for command in commands:
                with self.subTest(command=command):
                    result = run_cli(*command, str(path), timeout=60)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    if diagnostic:
                        self.assertIn(diagnostic, result.stdout + result.stderr)
                    self.assertNotEqual('feature enabled\n', result.stdout)

    def native(self, path, directory):
        emitted = run_cli('emit-c', str(path), timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stderr)
        c_file = Path(directory) / 'program.c'
        executable = Path(directory) / 'program'
        c_file.write_text(emitted.stdout)
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                                    '-I', str(RUNTIME), str(c_file), str(RUNTIME / 'fibril_runtime.c'),
                                    '-o', str(executable)], capture_output=True, text=True, timeout=120)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        result = subprocess.run([str(executable)], capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        return emitted.stdout, result.stdout

    def test_tracked_application_and_erasure_hosted_native(self):
        self.assertEqual(run_cli('check', str(EXAMPLE)).returncode, 0)
        checked = run_cli('check', '--json', str(EXAMPLE))
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertTrue(json.loads(checked.stdout)['accepted'])
        with tempfile.TemporaryDirectory(prefix='fibril-policy-native-') as directory:
            path = Path(directory) / 'program.fib'
            outputs = []
            for source in (SOURCE, SOURCE.replace(GUARD, '').replace(REQUIRES, '')):
                path.write_text(source)
                hosted = run_cli('run', str(path))
                self.assertEqual(hosted.returncode, 0, hosted.stderr)
                self.assertEqual(hosted.stdout, 'feature enabled\n')
                emitted, native_output = self.native(path, directory)
                self.assertEqual(native_output, hosted.stdout)
                evaluated = run_cli('eval', str(path))
                self.assertEqual(evaluated.returncode, 0, evaluated.stderr)
                outputs.append((emitted, evaluated.stdout))
            # No proof declarations/metadata in native output or ordinary term.
            self.assertEqual(outputs[0], outputs[1])
            self.assertNotIn('policyStable', outputs[0][0])

    def test_independent_baseline_and_implementation_changes(self):
        old = 'if enabled then True else False'
        new = 'if enabled then False else True'
        self.assert_rejected(SOURCE.replace(old, new, 1), 'not structurally identical')
        self.assert_rejected(SOURCE.replace('reviewed enabled = ' + old, 'reviewed enabled = ' + new),
                             'not structurally identical')
        # Both changed deliberately: a different, consistent policy really changes output.
        with tempfile.TemporaryDirectory(prefix='fibril-policy-changed-') as directory:
            path = Path(directory) / 'program.fib'
            path.write_text(SOURCE.replace(old, new))
            hosted = run_cli('run', str(path))
            self.assertEqual(hosted.returncode, 0, hosted.stderr)
            self.assertEqual(hosted.stdout, 'feature disabled\n')
            _, output = self.native(path, directory)
            self.assertEqual(output, hosted.stdout)

    def test_alpha_names_and_pure_unit_arrow_application(self):
        source = SOURCE.replace('reviewed enabled = if enabled', 'reviewed renamed = if renamed')
        # An identity ascription/application is supported literally, never reduced
        # to establish equality. Both independently authored bodies must match it.
        source = source.replace('if enabled then True else False',
                                '(\\(1 value : Bool) => value) (if enabled then True else False)')
        source = source.replace('if renamed then True else False',
                                '(\\(1 value : Bool) => value) (if renamed then True else False)')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.fib'
            path.write_text(source)
            result = run_cli('run', str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'feature enabled\n')
            unit = '''consume : (1 value : Unit) -> Bool
consume value = case value of () => True
baseline : (1 value : Unit) -> Bool
baseline value = case value of () => True
cubical stable : consume = baseline by refl
requires stable
main : Bool
main = consume ()
'''
            path.write_text(unit)
            result = run_cli('eval', str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('Normal: True', result.stdout)

    def test_gate_cannot_be_bypassed_by_alternate_commands(self):
        wrong = SOURCE.replace('reviewed enabled = if enabled then True else False',
                               'reviewed enabled = if enabled then False else True')
        commands = (('check',), ('check', '--erased'), ('eval',), ('run',),
                    ('emit-c',), ('emit-c-binary',), ('emit-c-interactive',))
        self.assert_rejected(wrong, 'not structurally identical', commands)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.fib'
            path.write_text(wrong)
            result = run_cli('check', '--json', str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(json.loads(result.stdout)['accepted'])

    def test_binding_order_unknowns_duplicates_and_consumption(self):
        cases = [
            (SOURCE.replace('allow = reviewed', 'missing = reviewed'), 'unknown or forward endpoint'),
            (SOURCE.replace(GUARD, '').replace('allow :', GUARD + 'allow :', 1), 'unknown or forward endpoint'),
            (SOURCE.replace(REQUIRES, 'requires missing\n'), 'unknown or forward proof'),
            (SOURCE.replace(GUARD, '') + GUARD, 'unknown or forward proof'),
            (SOURCE + '\nrequires policyStable\n', None),
            (SOURCE.replace(REQUIRES, REQUIRES + REQUIRES), None),
            (SOURCE.replace(GUARD, GUARD + GUARD), 'Duplicate declaration'),
            (SOURCE.replace('policyStable : allow', 'allow : allow'), 'Duplicate declaration'),
            (SOURCE.replace(REQUIRES, ''), 'unused proof'),
            (SOURCE.replace('if allow True', 'if True'), 'consumer must reference'),
            (SOURCE.replace('main = putStrLn', 'main = let (allow : Bool) = True in putStrLn')
                   .replace('if allow True', 'if allow'), 'consumer must reference'),
            (SOURCE.replace('if allow True', 'if policyStable'), 'Unbound name'),
            (SOURCE.replace('policyStable', 'putStrLn'), 'proof labels are not ordinary terms'),
        ]
        for source, diagnostic in cases:
            with self.subTest(source=source):
                self.assert_rejected(source, diagnostic)

    def test_no_beta_eta_quantity_or_face_escape(self):
        self.assert_rejected(SOURCE.replace('reviewed enabled = if enabled then True else False',
                                           'reviewed enabled = (\\(1 x : Bool) => x) (if enabled then True else False)'),
                             'not structurally identical')
        self.assert_rejected(SOURCE.replace('reviewed : (1 enabled', 'reviewed : (enabled'),
                             'types/quantities differ')
        for escape in ('by refl on bottom', 'by endpoint p i 0', 'by assume', 'by refl\n  face bottom'):
            self.assert_rejected(SOURCE.replace('by refl', escape))

    def test_unsupported_recursive_global_effect_resource_and_erased_endpoints(self):
        self.assert_rejected(SOURCE.replace('allow enabled = if enabled then True else False',
                                           'allow enabled = allow enabled'))
        self.assert_rejected('helper : Bool\nhelper = True\n' + SOURCE.replace(
            'allow enabled = if enabled then True else False', 'allow enabled = if enabled then helper else False'),
            'globals and recursion are unsupported')
        self.assert_rejected(SOURCE.replace('allow : (1 enabled : Bool) -> Bool\nallow enabled = if enabled then True else False',
                                           'allow : IO Unit\nallow = putStrLn "not run"'))
        self.assert_rejected(SOURCE.replace('allow : (1 enabled : Bool) -> Bool\nallow enabled = if enabled then True else False',
                                           'allow : (1 handle : FileHandle Unit) -> IO Unit\nallow handle = pure ()'))
        self.assert_rejected(SOURCE.replace('allow : (1 enabled', '0 allow : (1 enabled'),
                             'endpoints must be unrestricted')
        self.assert_rejected(SOURCE.replace('(1 enabled : Bool)', '(0 enabled : Bool)')
                                   .replace('if enabled then True else False', 'True'))
        # Pure fragment checking cannot launder a violation in the actual consumer.
        self.assert_rejected(SOURCE.replace('main : IO Unit\nmain =',
                                           'main : (0 ignored : Bool) -> IO Unit\nmain ignored =')
                                   .replace('if allow True', 'if allow ignored'), 'Runtime checking')

    def test_otherwise_valid_effect_endpoints_fail_the_pure_gate(self):
        source = '''action : IO Unit
action = putStrLn "must not execute"
baseline : IO Unit
baseline = putStrLn "must not execute"
cubical stable : action = baseline by refl
requires stable
main : IO Unit
main = action
'''
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'effect.fib'
            plain = source.replace('cubical stable : action = baseline by refl\n', '').replace('requires stable\n', '')
            path.write_text(plain)
            checked = run_cli('check', str(path))
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assert_rejected(source, 'endpoint type is not closed in the supported pure fragment',
                             (('check',), ('run',), ('emit-c',)))

    def test_project_and_import_routes_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix='fibril-policy-project-') as directory:
            root = Path(directory)
            path = root / 'Main.fib'
            for source in (SOURCE, 'module Main\n' + SOURCE):
                path.write_text(source)
                for command in ('check', 'eval', 'run', 'emit-c'):
                    result = run_cli(command, '--source-dir', directory, str(path), timeout=60)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn('currently require standalone files', result.stderr)
            report = run_cli('check', '--json', '--source-dir', directory, str(path))
            self.assertNotEqual(report.returncode, 0)
            structured = json.loads(report.stdout)
            self.assertFalse(structured['accepted'])
            self.assertEqual(structured['diagnostics'][0]['stage'], 'module-checking')
            self.assertEqual(structured['report'], [])
            (root / 'Guarded.fib').write_text('module Guarded\n' + SOURCE)
            path.write_text('module Main\nimport Guarded\nmain : IO Unit\nmain = putStrLn "no bypass"\n')
            result = run_cli('check', '--source-dir', directory, str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('currently require standalone files', result.stderr)
            # An import cannot silently select the standalone gate either.
            path.write_text('import Guarded\n' + SOURCE)
            result = run_cli('check', str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('requires --source-dir', result.stdout + result.stderr)

    def test_inspection_routes_explicitly_reject_metadata(self):
        for arguments in (('elaborate',), ('symbols',), ('reference', '4', '1'),
                          ('references', '4', '1'), ('definition', '4', '1'),
                          ('rename-preview', '4', '1', 'renamed')):
            with self.subTest(command=arguments):
                result = run_cli(*arguments, str(EXAMPLE))
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn('Cubical metadata inspection is unsupported', result.stdout + result.stderr)
                self.assertNotIn('"value"', result.stdout)

    def test_contextual_marker_words_do_not_reserve_ordinary_names(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'ordinary.fib'
            path.write_text('cubical : Bool\ncubical = True\nrequires : Bool\nrequires = cubical\n'
                            'main : Bool\nmain = requires\n')
            result = run_cli('eval', str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: True', result.stdout)

    def test_package_and_test_commands_reject_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'src').mkdir()
            (root / 'src/Main.fib').write_text('module Main\n' + SOURCE)
            (root / 'src/Policy').mkdir()
            (root / 'src/Policy/Tests.fib').write_text('module Policy.Tests\n' + SOURCE)
            manifest = root / 'fibril.yaml'
            manifest.write_text('schema: 1\nname: policy-guard\nmodule-prefix: Policy\n'
                                'source-dir: src\nfoundation: de-morgan\nentry: Main\ntests: Policy.Tests\n')
            for command in ('check', 'run', 'emit-c', 'test'):
                with self.subTest(command=command):
                    result = run_cli(command, '--package', str(manifest), timeout=60)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn('currently require standalone files', result.stdout + result.stderr)
            report = run_cli('check', '--json', '--package', str(manifest))
            self.assertNotEqual(report.returncode, 0)
            structured = json.loads(report.stdout)
            self.assertFalse(structured['accepted'])
            self.assertTrue(any('currently require standalone files' in diagnostic['message']
                                for diagnostic in structured['diagnostics']))

    def test_format_preserves_proof_syntax(self):
        result = run_cli('format', str(EXAMPLE))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(GUARD.strip(), result.stdout)
        self.assertIn(REQUIRES.strip(), result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.fib'
            path.write_text(result.stdout)
            checked = run_cli('check', str(path))
            self.assertEqual(checked.returncode, 0, checked.stderr)


class CubicalBoolCasesTests(unittest.TestCase):
    assert_rejected = CubicalApplicationTests.assert_rejected
    native = CubicalApplicationTests.native

    def test_different_syntax_all_commands_erasure_and_actual_runtime(self):
        commands = (('check',), ('check', '--erased'), ('check', '--json'))
        for command in commands:
            result = run_cli(*command, str(BOOL_EXAMPLE))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('verified pointwise Bool agreement', result.stdout)
            self.assertIn('not a cubical path', result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.fib'
            # The two actual inputs distinguish identity from any constant replacement.
            for flag, expected in (('True', 'feature enabled\n'), ('False', 'feature disabled\n')):
                variants = []
                for guarded in (True, False):
                    source = BOOL_SOURCE.replace('allow True', 'allow ' + flag)
                    if not guarded:
                        source = source.replace(BOOL_GUARD, '').replace(REQUIRES, '')
                    path.write_text(source)
                    hosted = run_cli('run', str(path))
                    self.assertEqual(hosted.returncode, 0, hosted.stderr)
                    self.assertEqual(hosted.stdout, expected)
                    emitted, native = self.native(path, directory)
                    self.assertEqual(native, expected)
                    evaluated = run_cli('eval', str(path))
                    self.assertEqual(evaluated.returncode, 0, evaluated.stderr)
                    variants.append((emitted, evaluated.stdout))
                self.assertEqual(variants[0], variants[1])
                self.assertNotIn('policyStable', variants[0][0])
        # Refl does not silently gain semantic conversion.
        self.assert_rejected(BOOL_SOURCE.replace('by boolCases', 'by refl'), 'not structurally identical')

    def test_each_wrong_constructor_fails_before_any_execution_or_emission(self):
        commands = (('check',), ('check', '--erased'), ('check', '--json'),
                    ('eval',), ('run',), ('emit-c',), ('emit-c-binary',), ('emit-c-interactive',))
        for body, constructor in (('if enabled then True else True', 'False'),
                                  ('if enabled then False else False', 'True')):
            wrong = BOOL_SOURCE.replace('reviewed enabled = if enabled then True else False',
                                        'reviewed enabled = ' + body)
            self.assert_rejected(wrong, 'boolCases disagreement at ' + constructor, commands)

    def test_nested_conditions_and_unrestricted_permissions(self):
        variants = [BOOL_SOURCE.replace('if enabled then True else False',
                                       'if (if enabled then False else True) then False else True'),
                    BOOL_SOURCE.replace('(1 enabled : Bool)', '(enabled : Bool)')
                               .replace('allow enabled = enabled',
                                        'allow enabled = if enabled then enabled else enabled')]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'program.fib'
            for source in variants:
                path.write_text(source)
                checked = run_cli('check', str(path))
                self.assertEqual(checked.returncode, 0, checked.stderr)
                result = run_cli('run', str(path))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, 'feature enabled\n')
            # Unrestricted discard is legal; linear discard is not.
            source = BOOL_SOURCE.replace('(1 enabled : Bool)', '(enabled : Bool)')
            source = source.replace('allow enabled = enabled', 'allow enabled = True')
            source = source.replace('if enabled then True else False', 'True')
            path.write_text(source)
            self.assertEqual(run_cli('check', str(path)).returncode, 0)

    def test_quantities_and_internal_uses_cannot_be_reflected(self):
        self.assert_rejected(BOOL_SOURCE.replace('reviewed : (1 enabled', 'reviewed : (enabled'),
                             'types/quantities differ')
        self.assert_rejected(BOOL_SOURCE.replace('allow enabled = enabled', 'allow enabled = True'),
                             'endpoint runtime checking failed')
        self.assert_rejected(BOOL_SOURCE.replace('allow enabled = enabled',
                                                'allow enabled = if enabled then enabled else enabled'),
                             'endpoint runtime checking failed')
        self.assert_rejected(BOOL_SOURCE.replace('(1 enabled : Bool)', '(0 enabled : Bool)'))
        self.assert_rejected(BOOL_SOURCE.replace('allow :', '0 allow :', 1),
                             'endpoints must be unrestricted')
        self.assert_rejected(BOOL_SOURCE.replace('main : IO Unit\nmain =',
                                                'main : (0 ignored : Bool) -> IO Unit\nmain ignored =')
                                       .replace('allow True', 'allow ignored'), 'Runtime checking')

    def test_fragment_is_exact_no_apps_globals_recursion_effects_or_higher_order(self):
        self.assert_rejected(BOOL_SOURCE.replace('allow enabled = enabled',
                                                'allow enabled = (\\(1 x : Bool) => x) enabled'),
                             'boolCases left endpoint unsupported')
        self.assert_rejected(BOOL_SOURCE.replace('allow enabled = enabled', 'allow enabled = allow enabled'),
                             'Unbound name')
        self.assert_rejected('helper : Bool\nhelper = True\n' + BOOL_SOURCE.replace(
            'allow enabled = enabled', 'allow enabled = if enabled then helper else False'),
                             'globals and recursion are unsupported')
        for signature, body, main in (('IO Unit', 'putStrLn "not run"', 'action'),
                                       ('(1 x : Unit) -> Bool', 'True', 'action ()'),
                                       ('Bool -> Bool -> Bool', '\\x => \\y => x', 'action True False')):
            # Unit/function cases may fail independent quantitative checking first;
            # use unrestricted arguments where a body discards its input.
            signature = signature.replace('(1 x : Unit)', '(x : Unit)')
            args = ' x' if signature.startswith('(x : Unit)') else ''
            source = (f'action : {signature}\naction{args} = {body}\n'
                      f'baseline : {signature}\nbaseline{args} = {body}\n'
                      'cubical stable : action = baseline by boolCases\n'
                      f'requires stable\nmain : {"IO Unit" if signature == "IO Unit" else "Bool"}\nmain = {main}\n')
            self.assert_rejected(source)
        self.assert_rejected(BOOL_SOURCE.replace('allow : (1 enabled : Bool) -> Bool\nallow enabled = enabled',
                             'allow : (1 handle : FileHandle Unit) -> IO Unit\nallow handle = pure ()'))

    def test_metadata_binding_format_and_no_alternate_route(self):
        cases = [(BOOL_SOURCE.replace('allow = reviewed', 'missing = reviewed'), 'unknown or forward endpoint'),
                 (BOOL_SOURCE.replace(REQUIRES, ''), 'unused proof'),
                 (BOOL_SOURCE.replace('allow True', 'True'), 'consumer must reference'),
                 (BOOL_SOURCE.replace('policyStable', 'putStrLn'), 'proof labels are not ordinary terms'),
                 (BOOL_SOURCE.replace('main = putStrLn', 'main = let (allow : Bool) = True in putStrLn')
                             .replace('allow True', 'allow'), 'consumer must reference'),
                 (BOOL_SOURCE.replace('by boolCases', 'by boolCases on bottom'), None)]
        for source, diagnostic in cases:
            self.assert_rejected(source, diagnostic)
        formatted = run_cli('format', str(BOOL_EXAMPLE))
        self.assertEqual(formatted.returncode, 0, formatted.stderr)
        self.assertIn(BOOL_GUARD.strip(), formatted.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(formatted.stdout)
            self.assertEqual(run_cli('check', str(path)).returncode, 0)
            for command in ('check', 'eval', 'run', 'emit-c'):
                rejected = run_cli(command, '--source-dir', directory, str(path))
                self.assertNotEqual(rejected.returncode, 0)
                self.assertIn('currently require standalone files', rejected.stderr)
            inspected = run_cli('symbols', str(path))
            self.assertNotEqual(inspected.returncode, 0)
            self.assertIn('Cubical metadata inspection is unsupported', inspected.stderr)

    def test_shared_body_node_allowance_fails_closed(self):
        body = 'enabled'
        for _ in range(8):
            body = f'if True then ({body}) else ({body})'
        source = BOOL_SOURCE.replace('(1 enabled : Bool)', '(enabled : Bool)')
        source = source.replace('allow enabled = enabled', 'allow enabled = ' + body)
        source = source.replace('if enabled then True else False', body)
        self.assert_rejected(source, 'shared body-node allowance exhausted')


if __name__ == '__main__':
    unittest.main()
