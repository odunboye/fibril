#!/usr/bin/env python3
"""Smoke-test the built CLI independently of its pure implementation helpers."""
from pathlib import Path
import subprocess
import tempfile
import random
import unittest
import json
import os
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "build/exec/fibril"


def run(*args, cwd=ROOT):
    return subprocess.run([str(EXE), *args], cwd=cwd, text=True,
                          capture_output=True, timeout=20)


class CLITests(unittest.TestCase):
    def test_help(self):
        result = run("--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("fibril demo", result.stdout)
        self.assertIn("not implemented yet", result.stdout)

    def test_local_packages_check_run_and_permission_boundaries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def package(name, prefix, deps=(), entry=False):
                folder = root / name
                (folder / 'src').mkdir(parents=True, exist_ok=True)
                text = (f'schema: 1\nname: {name}\nmodule-prefix: {prefix}\nsource-dir: src\nfoundation: de-morgan\n' +
                        ('entry: Main\n' if entry else '') + 'dependencies:\n' +
                        (''.join(f'  {key}:\n    path: {path}\n' for key, path in deps) if deps else '  {}\n'))
                (folder / 'fibril.yaml').write_text(text)
                return folder
            def source(folder, module, body):
                path = folder / 'src' / (module.replace('.', '/') + '.fib')
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('module ' + module + '\n' + body)
                return path
            core = package('core', 'Core')
            mail = package('mail', 'Mail', [('core', '../core')], entry=True)
            app = package('app', 'App', [('mail', '../mail')], entry=True)
            core_source = source(core, 'Core.Text', '\nexport\nvalue : String\nvalue = "core"\n')
            mail_source = source(mail, 'Mail.Queue', 'import Core.Text\n\nexport\nmessage : String\nmessage = Core.Text.value\n')
            # A dependency entry must never become the application's entry.
            source(mail, 'Main', '\nnot valid source\n')
            app_source = source(app, 'Main', 'import Mail.Queue\n\nmain : IO Unit\nmain = putStrLn Mail.Queue.message\n')
            manifest = app / 'fibril.yaml'
            original = manifest.read_text()
            result = run('run', '--package', str(manifest), cwd=root)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'core\n')
            checked = run('check', '--package', str(manifest), cwd=app)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertIn('Modules: 3', checked.stdout)
            graph = run('module-graph', '--package', str(manifest))
            self.assertEqual(graph.returncode, 0, graph.stdout + graph.stderr)
            scope = json.loads(graph.stdout)['package_scope']
            self.assertEqual(scope['entry_package'], 'app')
            self.assertEqual([spec['name'] for spec in scope['inventory']], ['app', 'core', 'mail'])
            self.assertEqual({item['owner'] for item in scope['module_owners']}, {'app', 'core', 'mail'})
            # Core has already entered the graph cache through Mail: app still has no permission.
            app_source.write_text(app_source.read_text().replace('import Mail.Queue', 'import Mail.Queue\nimport Core.Text'))
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            # Explicit direct permission creates a shared diamond, not duplicated graphs.
            manifest.write_text(original + '  core:\n    path: ../core\n')
            checked = run('check', '--package', str(manifest))
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertIn('Modules: 3', checked.stdout)
            # Package permission alone does not expose unimported source module bindings.
            app_source.write_text('module Main\nimport Mail.Queue\n\nmain : IO Unit\nmain = putStrLn Core.Text.value\n')
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            app_source.write_text('module Main\nimport Mail.Queue\n\nmain : IO Unit\nmain = putStrLn Mail.Queue.message\n')
            original_mail_source = mail_source.read_text()
            mail_source.write_text(original_mail_source + '\nbroken : String\nbroken = true\n')
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            mail_source.write_text(original_mail_source)
            # A cached manifest must validate every incoming dependency key.
            manifest.write_text(original + '  alias:\n    path: ../core\n')
            result = run('check', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Dependency key', result.stderr)
            manifest.write_text(original)
            # Invalid manifest in an unimported declared dependency still rejects before effects.
            app_source.write_text('module Main\n\nmain : IO Unit\nmain = putStrLn "before"\n')
            core_manifest = core / 'fibril.yaml'
            core_text = core_manifest.read_text()
            core_manifest.write_text(core_text + 'scripts: {}\n')
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            core_manifest.write_text(core_text)
            # A package cycle is rejected even without a source-module cycle.
            core_manifest.write_text(core_text.replace('  {}\n', '  app:\n    path: ../app\n'))
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('cycle', result.stderr.lower())
            core_manifest.write_text(core_text)
            # Prefix selection is component-wise and never falls back to another source root.
            app_source.write_text('module Main\nimport CoreMissing.Text\n\nmain : IO Unit\nmain = putStrLn "before"\n')
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')

    def test_local_packages_canonical_roots_and_exact_case(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            app = root / 'mail app 日本'
            (app / 'src').mkdir(parents=True)
            (app / 'src/Main.fib').write_text('module Main\n\nmain : IO Unit\nmain = putStrLn "ok"\n')
            manifest = app / 'fibril.yaml'
            baseline = 'schema: 1\nname: app\nmodule-prefix: App\nsource-dir: src\nfoundation: de-morgan\nentry: Main\n'
            manifest.write_text(baseline)
            self.assertEqual(run('run', '--package', 'fibril.yaml', cwd=app).stdout, 'ok\n')
            self.assertNotEqual(run('check', '--package', str(app / 'Fibril.yaml')).returncode, 0)
            self.assertNotEqual(run('check', '--package', str(root / 'MAIL APP 日本/fibril.yaml')).returncode, 0)
            self.assertNotEqual(run('check', '--package', str(app / 'fibril.yaml').replace('mail app', 'Mail app')).returncode, 0)
            for text in [baseline.replace('source-dir: src', 'source-dir: Src'),
                         baseline.replace('entry: Main\n', ''), baseline + 'dependencies:\n  absent:\n    path: ../absent\n']:
                manifest.write_text(text)
                result = run('run', '--package', str(manifest))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')
            # A contained lexical path can still escape through a symlink.
            (root / 'outside').mkdir()
            (app / 'escape').symlink_to(root / 'outside', target_is_directory=True)
            manifest.write_text(baseline.replace('source-dir: src', 'source-dir: escape'))
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('escapes', result.stderr)
            # Canonical roots cannot alias/nest, even if namespace ownership is disjoint.
            dep = app / 'src/nested-package'
            (dep / 'src').mkdir(parents=True)
            (dep / 'fibril.yaml').write_text(baseline.replace('name: app', 'name: dep').replace('module-prefix: App', 'module-prefix: Dep'))
            manifest.write_text(baseline + 'dependencies:\n  dep:\n    path: src/nested-package\n')
            result = run('run', '--package', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('alias or nest', result.stderr)
            manifest.write_text(baseline)
            # Same-directory filename aliases must fail too (not merely relocation aliases).
            same_dir_alias = app / 'alias.yaml'
            same_dir_alias.symlink_to(manifest)
            result = run('check', '--package', str(same_dir_alias))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('filename must be exactly', result.stderr)
            # Manifest-file symlinks must not relocate relative dependencies silently.
            link = root / 'alias'
            link.mkdir()
            (link / 'fibril.yaml').symlink_to(manifest)
            result = run('run', '--package', str(link / 'fibril.yaml'))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('manifest-file symlink', result.stderr)

    def test_local_package_discovery_and_global_source_admission(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def manifest(index, targets):
                folder = root / f'pkg-{index}'
                (folder / 'src').mkdir(parents=True, exist_ok=True)
                text = (f'schema: 1\nname: pkg-{index}\nmodule-prefix: P{index}\nsource-dir: src\nfoundation: de-morgan\n' +
                        ('entry: Main\n' if index == 0 else '') + 'dependencies: ' +
                        ('\n' + ''.join(f'  pkg-{target}:\n    path: ../pkg-{target}\n' for target in targets) if targets else '{}\n'))
                (folder / 'fibril.yaml').write_text(text)
            for index in range(65):
                manifest(index, [])
            main = root / 'pkg-0/src/Main.fib'
            main.write_text('module Main\n\nmain : IO Unit\nmain = putStrLn "bounded"\n')
            path = root / 'pkg-0/fibril.yaml'
            manifest(0, range(1, 64))
            result = run('check', '--package', str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            manifest(0, range(1, 65))
            result = run('run', '--package', str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('package admission', result.stderr)
            manifest(0, range(1, 64))
            for index in (1, 2, 3):
                manifest(index, range(index + 1, 64))
            manifest(4, range(5, 15))  # 63 + 62 + 61 + 60 + 10 = 256 retained edges.
            result = run('check', '--package', str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            manifest(4, range(5, 16))
            result = run('check', '--package', str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('edge admission', result.stderr)
            for index in (1, 2, 3, 4):
                manifest(index, [])
            too_large = root / 'pkg-1/fibril.yaml'
            saved = too_large.read_bytes()
            too_large.write_bytes(saved + b'#' + b'.' * (8193 - len(saved) - 1))
            result = run('run', '--package', str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('8192-byte', result.stderr)
            too_large.write_bytes(saved)
            for index in range(1, 33):
                folder = root / f'pkg-{index}/src/P{index}'
                folder.mkdir()
                (folder / 'Value.fib').write_text(f'module P{index}.Value\n\nexport\nvalue : String\nvalue = "value"\n')
            for count, accepted in ((31, True), (32, False)):
                main.write_text('module Main\n' + ''.join(f'import P{index}.Value\n' for index in range(1, count + 1)) +
                                '\nmain : IO Unit\nmain = putStrLn "bounded"\n')
                result = run('run', '--package', str(path))
                self.assertEqual(result.returncode == 0, accepted, result.stdout + result.stderr)
                if not accepted:
                    self.assertEqual(result.stdout, '')
                    self.assertIn('Module count', result.stderr)
            # Aggregate bytes remain a single budget across distinct owning roots.
            main.write_text('module Main\n' + ''.join(f'import P{index}.Value\n' for index in range(1, 9)) +
                            '\nmain : IO Unit\nmain = putStrLn "bounded"\n')
            for index in range(1, 9):
                file = root / f'pkg-{index}/src/P{index}/Value.fib'
                content = file.read_bytes()
                limit = 65536 if index < 8 else 65536 - len(main.read_bytes())
                file.write_bytes(content + b'--' + b'.' * (limit - len(content) - 2))
            result = run('check', '--package', str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            last = root / 'pkg-8/src/P8/Value.fib'
            last.write_bytes(last.read_bytes() + b'.')
            result = run('run', '--package', str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('Aggregate module source byte', result.stderr)

    def test_current_directory_package_commands_do_not_search_parents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            created = run('new', 'parent', cwd=root)
            self.assertEqual(created.returncode, 0, created.stdout + created.stderr)
            project = root / 'parent'
            for command in ('check', 'run', 'module-graph'):
                bare = run(command, cwd=project)
                explicit = run(command, '--package', 'fibril.yaml', cwd=project)
                self.assertEqual(bare.returncode, 0, bare.stdout + bare.stderr)
                self.assertEqual(bare.stdout, explicit.stdout)
            nested = project / 'nested'
            nested.mkdir()
            for command in ('check', 'run', 'module-graph'):
                missing = run(command, cwd=nested)
                self.assertNotEqual(missing.returncode, 0)
                self.assertEqual(missing.stdout, '')
                self.assertIn('fibril.yaml', missing.stderr)
            self.assertEqual(run('run', '--package', '../fibril.yaml', cwd=nested).stdout, 'Hello from parent!\n')
            # An invalid local manifest must not fall back to the valid parent.
            (nested / 'fibril.yaml').write_text('schema: 999\n')
            for command in ('check', 'run', 'module-graph'):
                invalid = run(command, cwd=nested)
                self.assertNotEqual(invalid.returncode, 0)
                self.assertEqual(invalid.stdout, '')
            # Explicit source operands retain their meaning despite a malformed manifest.
            standalone = nested / 'standalone.fib'
            (nested / "Main.fib").write_text('module Main\n\nmain : IO Unit\nmain = putStrLn "explicit root"\n')
            self.assertEqual(run('run', '--source-dir', '.', 'Main.fib', cwd=nested).stdout, 'explicit root\n')
            standalone.write_text('main : IO Unit\nmain = putStrLn "standalone"\n')
            self.assertEqual(run('run', 'standalone.fib', cwd=nested).stdout, 'standalone\n')
            # A valid nested project is selected instead of its parent.
            (nested / 'fibril.yaml').unlink()
            self.assertEqual(run('new', 'child', cwd=nested).returncode, 0)
            self.assertEqual(run('run', cwd=nested / 'child').stdout, 'Hello from child!\n')

    def test_standalone_library_scaffold_check_and_bool_tests(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for args in [ ['bad', '--lib', '--lib'], ['bad', '--lib', '--source-only'],
                          ['bad', '--source-only', '--lib'],
                          ['bad', '--lib', '--module-prefix', '.'.join(['A'] * 17)],
                          ['bad', '--lib', '--module-prefix', 'A' * 1025] ]:
                result = run('new', *args, cwd=root)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(list(root.iterdir()), [])
            preview = run('new', 'email-core', '--lib', '--module-prefix', 'Email.Core', '--dry-run', cwd=root)
            self.assertEqual(preview.returncode, 0, preview.stdout + preview.stderr)
            self.assertIn('test/src/TestSuite/Suite.fib', preview.stdout)
            self.assertEqual(list(root.iterdir()), [])
            result = run('new', 'email-core', '--lib', '--module-prefix', 'Email.Core', cwd=root)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            project = root / 'email-core'
            metadata = json.loads(run('manifest', 'fibril.yaml', cwd=project).stdout)
            self.assertIsNone(metadata['entry'])
            self.assertEqual(metadata['modules'], ['Email.Core'])
            self.assertEqual(metadata['test_package'], 'test')
            self.assertFalse((project / 'src/Main.fib').exists())
            checked = run('check', cwd=project)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertIn('no runtime entry', checked.stdout)
            graph = run('module-graph', cwd=project)
            self.assertEqual(graph.returncode, 0, graph.stdout + graph.stderr)
            self.assertIsNone(json.loads(graph.stdout)['entry'])
            self.assertNotEqual(run('run', cwd=project).returncode, 0)
            tested = run('test', '--package', str(project / 'fibril.yaml'), cwd=root)
            self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
            self.assertIn('Tests: passed', tested.stdout)
            suite = project / 'test/src/TestSuite/Suite.fib'
            baseline = suite.read_text()
            suite.write_text('module TestSuite.Suite\n\nmain : Bool\nmain = False\n')
            self.assertEqual(run('check', cwd=project).returncode, 0)  # check never evaluates suites
            failed = run('test', cwd=project)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(failed.stdout, '')
            self.assertIn('Tests: failed', failed.stderr)
            suite.write_text('module TestSuite.Suite\n\nmain : IO Unit\nmain = putStrLn "MUST NOT EXECUTE"\n')
            failed = run('test', cwd=project)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(failed.stdout, '')
            self.assertIn('main : Bool', failed.stderr)
            suite.write_text(baseline)
            manifest = project / 'fibril.yaml'
            manifest.write_text(manifest.read_text() + 'entry: Main\n')
            (project / 'src/Main.fib').write_text('module Main\n\nmain : IO Unit\nmain = putStrLn "MUST NOT EXECUTE"\n')
            tested = run('test', cwd=project)
            self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
            self.assertNotIn('MUST NOT EXECUTE', tested.stdout)

    def test_library_inventory_coverage_visibility_and_schema(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertEqual(run('new', 'lib', '--lib', '--module-prefix', 'Lib', cwd=root).returncode, 0)
            project = root / 'lib'
            manifest = project / 'fibril.yaml'
            baseline = manifest.read_text()
            extra = project / 'src/Lib/Extra.fib'
            extra.write_text('module Lib.Extra\n\nbroken : String\nbroken = True\n')
            manifest.write_text(baseline.replace('modules: ["Lib"]', 'modules: ["Lib", "Lib.Extra"]'))
            for command in ('check', 'test'):
                rejected = run(command, cwd=project)
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            extra.write_text('module Lib.Extra\n\nexport\nvalue : Bool\nvalue = True\n')
            suite = project / 'test/src/TestSuite/Suite.fib'
            suite.write_text('module TestSuite.Suite\n\nmain : Bool\nmain = Lib.Extra.value\n')
            self.assertNotEqual(run('test', cwd=project).returncode, 0)  # inventory is not an import
            suite.write_text('module TestSuite.Suite\nimport Lib.Extra\n\nmain : Bool\nmain = Lib.Extra.value\n')
            self.assertEqual(run('test', cwd=project).returncode, 0)
            manifest.write_text(baseline.replace('modules: ["Lib"]', 'modules: ["Lib.Extra", "Lib"]'))
            tested = run('test', cwd=project)
            self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
            extra.write_text('module Lib.Extra\nimport TestSuite.Suite\n\nvalue : Bool\nvalue = True\n')
            self.assertNotEqual(run('test', cwd=project).returncode, 0)  # terminal suite policy
            for value in ['{}', 'true', '[["Lib"]]', '[true]', '["Main"]', '["LibExtra"]', '["Lib", "Lib"]']:
                manifest.write_text(baseline.replace('modules: ["Lib"]', 'modules: ' + value))
                self.assertNotEqual(run('manifest', 'fibril.yaml', cwd=project).returncode, 0)
            manifest.write_text(baseline.replace('modules: ["Lib"]\n', ''))
            self.assertNotEqual(run('check', cwd=project).returncode, 0)
            self.assertNotEqual(run('test', cwd=project).returncode, 0)
            manifest.write_text(baseline.replace('test-package: test', 'tests: ["Lib.Tests"]'))
            self.assertNotEqual(run('manifest', 'fibril.yaml', cwd=project).returncode, 0)

    def test_library_bool_suite_fuel_exhaustion_is_an_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertEqual(run('new', 'slow', '--lib', cwd=root).returncode, 0)
            project = root / 'slow'
            module = project / 'src/App.fib'
            text = module.read_text()
            for index in range(7):
                text += ('\nexport\n' if index == 6 else '\n')
                text += f'f{index} : (1 value : Bool) -> Bool\n'
                body = 'value' if index == 0 else f'f{index-1} (f{index-1} value)'
                text += f'f{index} = \\(1 value : Bool) => {body}\n'
            module.write_text(text)
            (project / 'test/src/TestSuite/Suite.fib').write_text('module TestSuite.Suite\nimport App\n\nmain : Bool\nmain = App.f6 True\n')
            result = run('test', cwd=project)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('fuel exhausted', result.stderr)

    def test_transitive_package_inventories_share_checking_and_source_budgets(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, owned in [('core', 'Core'), ('middle', 'Middle'), ('app', 'App')]:
                result = run('new', name, '--lib', '--module-prefix', owned, cwd=root)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for name, dependency in [('app', 'middle'), ('middle', 'core')]:
                file = root / name / 'fibril.yaml'
                file.write_text(file.read_text().replace('dependencies: {}', f'dependencies:\n  {dependency}:\n    path: ../{dependency}'))
            app = root / 'app'
            core_source = root / 'core/src/Core.fib'
            original = core_source.read_text()
            core_source.write_text(original + '\nbroken : String\nbroken = True\n')
            for command in ('check', 'test'):
                failed = run(command, cwd=app)
                self.assertNotEqual(failed.returncode, 0)
                self.assertEqual(failed.stdout, '')
                self.assertIn('Core.fib', failed.stderr)
            core_source.write_text(original)
            for command in ('check', 'test'):
                accepted = run(command, cwd=app)
                self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
            suite = app / 'test/src/TestSuite/Suite.fib'
            original_suite = suite.read_text()
            suite.write_text(original_suite.replace('import App', 'import App\nimport Core'))
            self.assertNotEqual(run('test', cwd=app).returncode, 0)  # seeded does not grant transitive permission
            suite.write_text(original_suite)
            for name, owned, count in [('core', 'Core', 10), ('middle', 'Middle', 10), ('app', 'App', 12)]:
                file = root / name / 'fibril.yaml'
                names = [owned] + [f'{owned}.M{i}' for i in range(count - 1)]
                for module in names[1:]:
                    path = root / name / 'src' / (module.replace('.', '/') + '.fib')
                    path.write_text(f'module {module}\n\nvalue : Bool\nvalue = True\n')
                file.write_text(file.read_text().replace(f'modules: ["{owned}"]', 'modules: ' + json.dumps(names)))
            checked = run('check', cwd=app)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertIn('Modules: 32', checked.stdout)
            tested = run('test', cwd=app)  # selected suite is the 33rd distinct module, not a fresh budget
            self.assertNotEqual(tested.returncode, 0)
            self.assertEqual(tested.stdout, '')
            self.assertIn('admission exhausted', tested.stderr)

    def test_new_app_has_registered_starter_bool_suite(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            preview = run('new', 'hello', '--dry-run', cwd=root)
            self.assertEqual(preview.returncode, 0, preview.stderr)
            self.assertIn('hello/test/src/TestSuite/Suite.fib', preview.stdout)
            self.assertEqual(list(root.iterdir()), [])
            created = run('new', 'hello', cwd=root)
            self.assertEqual(created.returncode, 0, created.stdout + created.stderr)
            self.assertIn('fibril test', created.stdout)
            project = root / 'hello'
            self.assertEqual((project / 'test/src/TestSuite').stat().st_mode & 0o777, 0o700)
            metadata = json.loads(run('manifest', 'fibril.yaml', cwd=project).stdout)
            self.assertEqual(metadata['entry'], 'Main')
            self.assertEqual(metadata['test_package'], 'test')
            self.assertEqual(run('run', cwd=project).stdout, 'Hello from hello!\n')
            checked = run('check', cwd=project)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            tested = run('test', cwd=project)
            self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
            self.assertIn('Tests: passed', tested.stdout)
            self.assertNotIn('Hello from', tested.stdout)
            suite = project / 'test/src/TestSuite/Suite.fib'
            suite.write_text(suite.read_text().replace('main = True', 'main = False'))
            failed = run('test', cwd=project)
            self.assertNotEqual(failed.returncode, 0)
            self.assertEqual(failed.stdout, '')
            self.assertIn('Tests: failed', failed.stderr)
            self.assertEqual(run('check', cwd=project).returncode, 0)
            self.assertIn('does not verify application IO', (project / 'README.md').read_text())

    def test_separate_test_package_boundaries_and_legacy_suites(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertEqual(run('new', 'lib', '--lib', '--module-prefix', 'TestSuite', cwd=root).returncode, 0)
            project = root / 'lib'
            manifest = project / 'fibril.yaml'
            child = project / 'test/fibril.yaml'
            metadata = json.loads(run('manifest', str(child)).stdout)
            self.assertEqual(metadata['module_prefix'], 'SpecSuite')
            self.assertEqual(metadata['dependencies'], [{'name': 'lib', 'path': '..'}])
            self.assertEqual(run('test', cwd=project).returncode, 0)
            suite = project / 'test/src/SpecSuite/Suite.fib'
            suite.write_text('module SpecSuite.Suite\nimport TestSuite\n\nmain : Bool\nmain = TestSuite.privateValue\n')
            source = project / 'src/TestSuite.fib'
            source.write_text(source.read_text() + '\nprivateValue : Bool\nprivateValue = True\n')
            self.assertNotEqual(run('test', cwd=project).returncode, 0)
            child_text = child.read_text()
            child.write_text(child_text.replace('dependencies:\n  "lib":\n    path: ..', 'dependencies: {}'))
            missing = run('test', cwd=project)
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn('directly depend', missing.stderr)
            child.write_text(child_text)
            other = root / 'other'
            (other / 'src').mkdir(parents=True)
            (other / 'fibril.yaml').write_text(manifest.read_text().replace('test-package: test\n', ''))
            child.write_text(child_text.replace('path: ..', 'path: ../../other'))
            wrong_parent = run('test', cwd=project)
            self.assertNotEqual(wrong_parent.returncode, 0)
            self.assertIn('same canonical parent', wrong_parent.stderr)
            child.write_text(child_text)
            outside = root / 'outside'
            outside.mkdir()
            (project / 'escape').symlink_to(outside, target_is_directory=True)
            (outside / 'src').mkdir()
            (outside / 'fibril.yaml').write_text(child_text.replace('path: ..', 'path: ../lib'))
            manifest.write_text(manifest.read_text().replace('test-package: test', 'test-package: escape'))
            escaped = run('test', cwd=project)
            self.assertNotEqual(escaped.returncode, 0)
            self.assertIn('inside the parent package', escaped.stderr)
            manifest.write_text(manifest.read_text().replace('test-package: escape', 'test-package: test'))
            parent_text = manifest.read_text()
            for value in ('../outside', '/outside', '.', 'test/../outside'):
                manifest.write_text(parent_text.replace('test-package: test', 'test-package: ' + value))
                self.assertNotEqual(run('test', cwd=project).returncode, 0)
            manifest.write_text(parent_text + 'tests: TestSuite.Check\n')
            self.assertNotEqual(run('manifest', str(manifest)).returncode, 0)
            manifest.write_text(parent_text.replace('test-package: test', 'tests: TestSuite.Check'))
            (project / 'src/TestSuite/Check.fib').parent.mkdir(exist_ok=True)
            (project / 'src/TestSuite/Check.fib').write_text('module TestSuite.Check\n\nmain : Bool\nmain = True\n')
            self.assertEqual(run('test', cwd=project).returncode, 0)

    def test_new_source_only_scaffold(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            preview = run('new', 'plain', '--source-only', '--dry-run', cwd=root)
            self.assertEqual(preview.returncode, 0, preview.stderr)
            self.assertNotIn('fibril.yaml', preview.stdout)
            self.assertEqual(list(root.iterdir()), [])
            result = run('new', '--source-only', 'plain', cwd=root)
            self.assertEqual(result.returncode, 0, result.stderr)
            project = root / 'plain'
            self.assertFalse((project / 'fibril.yaml').exists())
            self.assertEqual(run('run', '--source-dir', 'src', 'src/Main.fib', cwd=project).stdout, 'Hello from plain!\n')

    def test_new_explicit_package_scaffold(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            preview = run('new', 'mailer', '--module-prefix', 'Mailer.Core', '--dry-run', cwd=root)
            self.assertEqual(preview.returncode, 0, preview.stdout + preview.stderr)
            self.assertIn('mailer/fibril.yaml', preview.stdout)
            self.assertEqual(list(root.iterdir()), [])
            for arguments in [
                ['mailer', '--source-only', '--source-only'],
                ['mailer', '--source-only', '--module-prefix', 'Mail'],
                ['mailer', '--module-prefix', 'Mail', '--source-only'],
                ['mailer', '--module-prefix'], ['mailer', '--module-prefix', 'Main'],
                ['mailer', '--module-prefix', 'Main.Core'], ['mailer', '--module-prefix', 'lower'],
                ['mailer', '--module-prefix', 'Mail..Core'], ['mailer', '--module-prefix', 'Mail/A'],
                ['mailer', '--module-prefix', 'A', '--module-prefix', 'B'],
                ['mailer', '--template', '--module-prefix', 'Mail', 'console'],
                ['mailer', '--module-prefix', '--dry-run'],
                ['mailer', '--module-prefix', '.'.join(['A'] * 17)],
                ['mailer', '--module-prefix', 'A' * 1025],
            ]:
                result = run('new', *arguments, cwd=root)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(list(root.iterdir()), [])
            for name, owned in [('mailer', 'Mailer.Core'), ('true', 'Null'), ('null', 'MainView'), ('long-owner', 'A' * 180)]:
                result = run('new', '--module-prefix', owned, name, '--template', 'console', cwd=root)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                folder = root / name
                self.assertEqual(sorted(p.name for p in folder.iterdir()), ['.gitignore', 'README.md', 'fibril.yaml', 'src', 'test'])
                inspected = run('manifest', 'fibril.yaml', cwd=folder)
                self.assertEqual(inspected.returncode, 0, inspected.stdout + inspected.stderr)
                metadata = json.loads(inspected.stdout)
                self.assertEqual(metadata['name'], name)
                self.assertEqual(metadata['module_prefix'], owned)
                self.assertEqual(metadata['dependencies'], [])
                self.assertEqual(metadata['test_package'], 'test')
                tested = run('test', cwd=folder)
                self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
                self.assertIn('Tests: passed', tested.stdout)
                checked = run('check', '--package', 'fibril.yaml', cwd=folder)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                executed = run('run', '--package', 'fibril.yaml', cwd=folder)
                self.assertEqual(executed.returncode, 0, executed.stdout + executed.stderr)
                self.assertEqual(executed.stdout, f'Hello from {name}!\n')
                self.assertIn('fibril check\nfibril run', (folder / 'README.md').read_text())
                before = (folder / 'fibril.yaml').read_bytes()
                self.assertNotEqual(run('new', name, '--module-prefix', owned, cwd=root).returncode, 0)
                self.assertEqual((folder / 'fibril.yaml').read_bytes(), before)

    def test_strict_local_manifest_inspection(self):
        baseline = ('schema: 1\nname: mailer-app\nmodule-prefix: Mailer\nsource-dir: src\n'
                    'foundation: de-morgan\nentry: Main\ndependencies:\n  email-core:\n    path: ../email-core\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "fibril.yaml"
            path.write_text(baseline)
            result = run("manifest", str(path), cwd=root)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = json.loads(result.stdout)
            self.assertFalse(report["checked"])
            self.assertFalse(report["resolved"])
            self.assertFalse(report["locked"])
            self.assertEqual(report["name"], "mailer-app")
            self.assertEqual(report["dependencies"], [{"name": "email-core", "path": "../email-core"}])
            self.assertEqual(sorted(p.name for p in root.iterdir()), ["fibril.yaml"])
            positives = [baseline.replace("source-dir: src", 'source-dir: "src/日本 語"'),
                         baseline.replace("module-prefix: Mailer", "module-prefix: MainView"),
                         baseline.replace("module-prefix: Mailer", "module-prefix: Text.Core"),
                         baseline.replace("\n", "\r\n"), baseline.replace("\n", "\r"),
                         '# comment\n---\n' + baseline,
                         baseline[:baseline.index("dependencies:")],
                         baseline[:baseline.index("dependencies:")] + 'dependencies: {}\n']
            for text in positives:
                path.write_bytes(text.encode("utf-8"))
                result = run("manifest", str(path), cwd=root)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            bads = [
                "", "# only a comment\n", "[]", "true", "null", baseline + "---\n",
                baseline + "---\n" + baseline, "%YAML 1.2\n---\n" + baseline,
                "%TAG !e! tag:example.org,2020:\n---\n" + baseline,
                "%FOO ignored\n---\n" + baseline, "\ufeff%YAML 1.2\n---\n" + baseline,
                "&root\n" + baseline,
                baseline.replace("name: mailer-app", "name: &name mailer-app"),
                baseline.replace("name: mailer-app", "name: *missing"),
                baseline.replace("name: mailer-app", "name: !!str mailer-app"),
                baseline.replace("name: mailer-app", "name: ! mailer-app"),
                baseline.replace("name: mailer-app", "name: !custom mailer-app"),
                baseline.replace("name: mailer-app", "name: |\n  mailer-app"),
                baseline.replace("name: mailer-app", "name: >\n  mailer-app"),
                baseline.replace("name: mailer-app", "name: true"),
                baseline.replace("source-dir: src", "source-dir: null"),
                baseline.replace("source-dir: src", "source-dir: 123"),
                baseline.replace("source-dir: src", "source-dir: [src]"),
                baseline.replace("source-dir: src", "source-dir: ''"),
                baseline.replace("source-dir: src", "source-dir: /src"),
                baseline.replace("source-dir: src", "source-dir: src/../lib"),
                baseline.replace("source-dir: src", "source-dir: src/./lib"),
                baseline.replace("source-dir: src", "source-dir: src/"),
                baseline.replace("schema: 1", 'schema: "1"'),
                baseline.replace("schema: 1", "schema: true"),
                baseline.replace("schema: 1", "schema: 1.0"),
                baseline.replace("schema: 1", "schema: +1"),
                baseline.replace("schema: 1", "schema: 0x1"),
                baseline.replace("schema: 1", "schema: 2"),
                baseline + "scripts: {}\n", baseline + "git: ignored\n",
                baseline + "name: duplicate\n", baseline + '"name": duplicate\n',
                baseline + '"na\\u006de": duplicate\n', baseline + "true: ignored\n",
                baseline + "? {nested: key}\n: ignored\n",
                baseline.replace("module-prefix: Mailer", "module-prefix: Main"),
                baseline.replace("module-prefix: Mailer", "module-prefix: Main.Library"),
                baseline.replace("module-prefix: Mailer", "module-prefix: lower"),
                baseline.replace("module-prefix: Mailer", "module-prefix: Mail..Core"),
                baseline.replace("foundation: de-morgan", "foundation: other"),
                baseline.replace("entry: Main", "entry: App.Main"),
                baseline.replace("    path: ../email-core", "    path: ../email-core\n    path: ../other"),
                baseline.replace("    path: ../email-core", "    path: ../email-core\n    url: ignored"),
                baseline.replace("  email-core:\n    path: ../email-core", "  email-core: ../email-core"),
                baseline.replace("  email-core:\n    path: ../email-core", "  email-core: {}"),
                baseline.replace("  email-core:\n    path: ../email-core", "  mailer-app:\n    path: ."),
                baseline[:baseline.index("dependencies:")] + 'dependencies: null\n',
                baseline + 'extra:\n  one:\n    two:\n      three: value\n',
                '[' * 65 + ']' * 65,
            ]
            for prefix in ("\t", "\t\t", "\t ", " \t"):
                for directive in ("%FOO ignored", "%YAML 1.2", "%TAG !e! tag:example.org,2020:"):
                    for newline in ("\n", "\r\n", "\r"):
                        bads.append(prefix + directive + newline + "---" + newline + baseline)
            for field in ("schema", "name", "module-prefix", "source-dir", "foundation"):
                bads.append("\n".join(line for line in baseline.splitlines() if not line.startswith(field + ":")))
            for escaped in (r'\0', r'\t', r'\n', r'\r', r'\x1b', r'\x7f', r'\u0085'):
                bads.append(baseline.replace("source-dir: src", f'source-dir: "src/{escaped}"'))
                bads.append(baseline.replace("path: ../email-core", f'path: "../{escaped}"'))
            for text in bads:
                with self.subTest(text=text[:120]):
                    path.write_bytes(text.encode("utf-8"))
                    result = run("manifest", str(path), cwd=root)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stdout, "")
                    self.assertEqual(sorted(p.name for p in root.iterdir()), ["fibril.yaml"])
            schema_error = baseline + 'scripts: {}\n'
            path.write_text(schema_error)
            result = run("manifest", str(path))
            self.assertIn("Unknown manifest field", result.stderr)
            self.assertNotIn("fibril.yaml:1:", result.stderr)
            # Independent admission boundaries; conservative raw guards are intentional.
            for count, expected in ((1024, 0), (1025, 1)):
                path.write_text(baseline.replace("source-dir: src", 'source-dir: "' + 'x' * count + '"'))
                self.assertEqual(run("manifest", str(path)).returncode == 0, expected == 0)
            for count, expected in ((128, 0), (129, 1)):
                path.write_text(baseline.replace("source-dir: src", 'source-dir: "' + '[' * count + '"'))
                self.assertEqual(run("manifest", str(path)).returncode == 0, expected == 0)
            for count, expected in ((256, 0), (257, 1)):
                path.write_text(baseline + '# comment\n' * (count - len(baseline.splitlines())))
                self.assertEqual(run("manifest", str(path)).returncode == 0, expected == 0)
            for count, expected in ((64, 0), (65, 1)):
                path.write_text(baseline[:baseline.index("dependencies:")] + 'dependencies:\n' +
                                ''.join(f'  pkg-{i}:\n    path: ../pkg-{i}\n' for i in range(count)))
                self.assertEqual(run("manifest", str(path)).returncode == 0, expected == 0)
            path.write_bytes(b'\xff')
            self.assertNotEqual(run("manifest", str(path)).returncode, 0)
            # Byte admission happens before file-buffer allocation and parser invocation.
            path.write_bytes((baseline + '#' + '.' * (8192 - len(baseline.encode()) - 1)).encode())
            self.assertEqual(run("manifest", str(path)).returncode, 0)
            path.write_bytes(path.read_bytes() + b'.')
            result = run("manifest", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("8192-byte read limit", result.stderr)
            # Event admission is separate from composition/schema checks.
            path.write_text('{' + ', '.join(f'k{i}: value' for i in range(260)) + '}')
            result = run("manifest", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("event admission", result.stderr)

    def test_new_console_project_is_offline_and_runnable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            dry = run("new", "mailer", "--template", "console", "--dry-run", cwd=root)
            self.assertEqual(dry.returncode, 0, dry.stdout + dry.stderr)
            self.assertIn("No filesystem checks or changes", dry.stdout)
            self.assertIn("mailer/fibril.yaml", dry.stdout)
            self.assertEqual(list(root.iterdir()), [])
            result = run("new", "--template", "console", "mailer", cwd=root)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            project = root / "mailer"
            self.assertEqual(sorted(str(p.relative_to(project)) for p in project.rglob("*") if p.is_file()),
                             [".gitignore", "README.md", "fibril.yaml", "src/Main.fib", "test/fibril.yaml", "test/src/TestSuite/Suite.fib"])
            self.assertEqual((project / "src/Main.fib").read_text(),
                             'module Main\n\nmain : IO Unit\nmain = putStrLn "Hello from mailer!"\n')
            self.assertEqual(project.stat().st_mode & 0o777, 0o700)
            self.assertEqual((project / "src").stat().st_mode & 0o777, 0o700)
            metadata = json.loads(run("manifest", "fibril.yaml", cwd=project).stdout)
            self.assertEqual(metadata["module_prefix"], "App")
            self.assertEqual(run("check", "--package", "fibril.yaml", cwd=project).returncode, 0)
            self.assertEqual(run("run", "--package", "fibril.yaml", cwd=project).stdout, "Hello from mailer!\n")
            self.assertFalse((project / ".git").exists())
            checked = run("check", "--source-dir", "src", "src/Main.fib", cwd=project)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            executed = run("run", "--source-dir", "src", "src/Main.fib", cwd=project)
            self.assertEqual(executed.returncode, 0, executed.stdout + executed.stderr)
            self.assertEqual(executed.stdout, "Hello from mailer!\n")
            again = run("new", "mailer", cwd=root)
            self.assertNotEqual(again.returncode, 0)
            self.assertEqual((project / "src/Main.fib").read_text(),
                             'module Main\n\nmain : IO Unit\nmain = putStrLn "Hello from mailer!"\n')

    def test_new_rejects_invalid_arguments_without_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for args in ([], ["../escape"], ["a/b"], ["a\\b"], ["Upper"], ["a b"],
                         ["a\n"], ["-x"], ["_x"], ["a" * 65], ["mailer", "extra"],
                         ["mailer", "--template"], ["mailer", "--template", "web"],
                         ["mailer", "--force"], ["mailer", "--dry-run", "--dry-run"],
                         ["mailer", "--template", "console", "--template", "console"]):
                with self.subTest(args=args):
                    result = run("new", *args, cwd=root)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertEqual(list(root.iterdir()), [])
            help_result = run("new", "--help", cwd=root)
            self.assertEqual(help_result.returncode, 0)
            self.assertEqual(list(root.iterdir()), [])

    def test_new_preserves_existing_entries_and_concurrent_admission(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "target"
            target.mkdir()
            (target / "sentinel").write_bytes(b"keep")
            (root / "existing").write_bytes(b"original")
            (root / "folder").mkdir()
            (root / "link").symlink_to(target, target_is_directory=True)
            (root / "dangling").symlink_to(root / "missing")
            for name in ("existing", "folder", "link", "dangling"):
                result = run("new", name, cwd=root)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            self.assertEqual((root / "existing").read_bytes(), b"original")
            self.assertEqual(list((root / "folder").iterdir()), [])
            self.assertTrue((root / "link").is_symlink())
            self.assertTrue((root / "dangling").is_symlink())
            self.assertEqual((target / "sentinel").read_bytes(), b"keep")
            self.assertEqual(sorted(p.name for p in target.iterdir()), ["sentinel"])
            with ThreadPoolExecutor(max_workers=2) as pool:
                futures = [pool.submit(run, "new", "racer", cwd=root) for _ in range(2)]
                results = [future.result() for future in futures]
            self.assertEqual(sorted(result.returncode for result in results), [0, 1])
            self.assertTrue((root / "racer/src/Main.fib").is_file())

    @unittest.skipIf(os.geteuid() == 0, "root bypasses directory permission checks")
    def test_new_permission_denial_has_no_partial_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            root.chmod(0o500)
            try:
                result = run("new", "denied", cwd=root)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertFalse((root / "denied").exists())
            finally:
                root.chmod(0o700)

    def test_version(self):
        result = run("--version")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Fibril 0.1.0-dev", result.stdout)

    def test_demo(self):
        result = run("demo")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for expected in ("Identity type: (Pi 0 Type0 (Pi 1 v0 v1))",
                         "Erased checking: accepted", "closed usage []",
                         "Linear duplication: rejected", "De Morgan interval law: passed",
                         "disjoint, not exhaustive", "not a soundness proof"):
            self.assertIn(expected, result.stdout)

    def test_source_loader_accepts_valid_unicode_and_empty_files(self):
        for text in ("", "identity x = x", "λ x → x\r\n", "日本語 🌊", "\ufffd"):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.fib"
                path.write_bytes(text.encode("utf-8"))
                result = run("validate-source", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("not type checked", result.stdout)

    def test_source_loader_rejects_bad_bytes_and_controls(self):
        for data, expected in ((b"\xff", "byte 0"),
                               (b"A\xe2\x82A", "byte 3"),
                               (b"\xed\xa0\x80", "surrogate"),
                               (b"\xf4\x90\x80\x80", "U+10FFFF"),
                               (b"x\x00", "control"),
                               ("x\u202e".encode("utf-8"), "bidirectional"),
                               (b"\xef\xbb\xbf", "marks")):
            with self.subTest(data=data), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.fib"
                path.write_bytes(data)
                result = run("validate-source", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected, result.stdout)

    def test_source_loader_limits_and_missing_file(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.fib"
            path.write_bytes(b"a" * 65536)
            self.assertEqual(run("validate-source", str(path)).returncode, 0)
            path.write_bytes(b"a" * 65537)
            result = run("validate-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("limit", result.stdout)
            path.unlink()
            self.assertNotEqual(run("validate-source", str(path)).returncode, 0)

    def test_malformed_bytes_agree_with_python_strict_rejection(self):
        rng = random.Random(3629)
        malformed = []
        while len(malformed) < 30:
            data = bytes(rng.randrange(256) for _ in range(rng.randint(1, 6)))
            try:
                data.decode("utf-8", errors="strict")
            except UnicodeDecodeError:
                malformed.append(data)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.fib"
            for data in malformed:
                with self.subTest(data=data):
                    path.write_bytes(data)
                    result = run("validate-source", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("UTF-8", result.stdout)

    def test_lexer_command_reports_tokens_and_rejects_unsupported_text(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expression.fib"
            path.write_text("λ x ⇒ x", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("1:1-1:2 lambda", result.stdout)
            self.assertIn("1:5-1:6 =>", result.stdout)
            path.write_text("x @ y", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("1:3", result.stdout)

    def test_source_check_command(self):
        result = run("check", "examples/core/identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertIn("(Pi 0 Type0 (Pi 1 v0 v1))", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expression.fib"
            path.write_text("Type 0", encoding="utf-8")
            self.assertNotEqual(run("check", str(path)).returncode, 0)
            result = run("check", "--erased", str(path))
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("no runtime-use guarantee", result.stdout)
            self.assertIn("Type: Type1", result.stdout)
            path.write_text("missing", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:1:1: Resolution:", result.stdout)
            self.assertIn("  1 | missing", result.stdout)
            self.assertIn("^", result.stdout)
            path.write_text("Type", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Parsing:", result.stdout)

    def test_ordinary_io_functions_and_portable_prelude(self):
        result = run("run", "examples/core/io-functions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "This is a Fibril library function.\n")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "shadow.fib"
            path.write_text(
                "putStrLn : Bool -> IO Unit\n"
                "putStrLn = \\(flag : Bool) => pure Unit ()\n"
                "main : IO Unit\nmain = putStrLn True\n", encoding="utf-8")
            result = subprocess.run([str(EXE), "run", str(path)], cwd=directory,
                                    text=True, capture_output=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "")
            path.write_text(
                "emit : (1 text : String) -> IO Unit\n"
                "emit = \\(1 text : String) => do\n"
                "  putStrLn text\n  putStrLn text\n"
                "main : IO Unit\nmain = emit \"linear\"\n", encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Binder usage", result.stderr)

    def test_console_pure_arguments(self):
        result = run("run", "examples/core/console-expressions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello from a pure function!\nString computation works.\nLocal bindings work too.\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/console-expressions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertNotIn("Hello from a pure function!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "arguments.fib"
            start = 'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
            for expression in ('True', 'missing', r'((\(1 x : String) => "discard") "input")',
                               r'((\(0 x : String) => x) "input")'):
                with self.subTest(expression=expression):
                    path.write_text(start + "  putStrLn " + expression + "\n", encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.write_text(start + "  putStrLn missing\n", encoding="utf-8")
            result = run("run", str(path))
            self.assertIn(f"{path}:4:12: Resolution:", result.stderr)
            self.assertIn("^", result.stderr)
            path.write_text(start + "  putStrLn True\n", encoding="utf-8")
            result = run("run", str(path))
            self.assertIn("inferred: Bool; expected: String", result.stderr)
            self.assertNotIn("^", result.stderr)

    def test_pure_string_program(self):
        result = run("check", "examples/core/string-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: String", result.stdout)
        result = run("eval", "examples/core/string-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: "Hello from pure Fibril."', result.stdout)
        result = run("run", "examples/core/string-identity.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("use eval", result.stderr)

    def test_structured_lambda_case_and_signature_layout(self):
        # Exact partially formatted report: don't skip an already-multiline RHS.
        source = (
            'module Patterns\nimport Data.Package\nimport Data.Message\n\n'
            '0 payloadType : (0 package : Data.Package.Package) -> Type 0\n'
            'payloadType = \\(0 package : Data.Package.Package) => case package return (\\(0 self : Data.Package.Package) => Type 0) of (0 Item : Type 0) (1 value : Item) => Item\n\n'
            'recover : (1 package : Data.Package.Package) -> payloadType package\n'
            'recover = \\(1 package : Data.Package.Package) => case package return (\\(0 self : Data.Package.Package) => payloadType self) of (0 Item : Type 0) (1 value : Item) => value\n\n'
            'main : IO Unit\nmain = putStrLn\n  (case Data.Message.MkMessage True\n'
            '    (recover\n      (Data.Package.MkPackage String "Patterns")) return (\\(0 self : Data.Message.Message) => String) of (1 enabled : Bool) (1 text : String) => if enabled then appendString text "!" else text)\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Patterns.fib"
            for ending in ("\n", "\r\n"):
                path.write_bytes(source.replace("\n", ending).encode())
                result = run("format", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('payloadType = \\(0 package : Data.Package.Package) =>\n  case package\n', result.stdout)
                self.assertIn('    of (0 Item : Type 0) (1 value : Item) =>\n      Item', result.stdout)
                self.assertIn('    of (1 enabled : Bool) (1 text : String) =>\n      if enabled', result.stdout)
                self.assertLessEqual(max(map(len, result.stdout.splitlines())), 100)
                path.write_bytes(result.stdout.replace("\n", ending).encode())
                again = run("format", str(path))
                self.assertEqual(again.stdout, result.stdout)
            # Signatures and long conditional branches, not only application groups.
            path.write_text(
                'combine : (0 Element : Type 0) -> (combine : (left : Element) -> (right : Element) -> Element) -> (left : Element) -> (middle : Element) -> (right : Element) -> Element\n'
                'combine = \\(0 Element : Type 0) => \\(combine : (left : Element) -> (right : Element) -> Element) => \\(left : Element) => \\(middle : Element) => \\(right : Element) => combine (combine left middle) right\n'
                'main : Bool\nmain = True\n')
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('->\n', result.stdout)
            self.assertIn('=>\n', result.stdout)
            path.write_text(result.stdout)
            self.assertEqual(run("format", str(path)).stdout, result.stdout)
            self.assertEqual(run("check", str(path)).returncode, 0)
            path.write_text(
                'main : String\nmain = if equalString "' + "a" * 40 + '" "' + "b" * 40 +
                '" then appendString "long branch" " value" else appendString "other branch" " value"\n')
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("\n  then ", result.stdout)
            self.assertIn("\n  else ", result.stdout)
            path.write_text(result.stdout)
            self.assertEqual(run("format", str(path)).stdout, result.stdout)
            self.assertEqual(run("check", str(path)).returncode, 0)
            # Verify the real dependency graph after applying the reported layout.
            for file in (ROOT / "examples/modules/records/Data").glob("*.fib"):
                destination = root / "Data" / file.name
                destination.parent.mkdir(exist_ok=True)
                destination.write_bytes(file.read_bytes())
            path.write_text(source)
            result = run("format", str(path))
            path.write_text(result.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Patterns!\n")

    def test_parenthesized_application_wrapping(self):
        source = ('module Main\nimport Data.Package\nimport Data.Message\n\nmain : IO Unit\n'
                  'main = putStrLn (Data.Message.render (Data.Message.MkMessage True (Data.Package.recover (Data.Package.MkPackage String "Records"))))\n')
        expected = ('module Main\nimport Data.Package\nimport Data.Message\n\nmain : IO Unit\n'
                    'main = putStrLn\n  (Data.Message.render\n    (Data.Message.MkMessage True\n'
                    '      (Data.Package.recover\n        (Data.Package.MkPackage String "Records"))))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Main.fib"
            for ending in ("\n", "\r\n"):
                for final in (False, True):
                    data = source.replace("\n", ending)
                    formatted = expected.replace("\n", ending)
                    if not final:
                        data = data[:-len(ending)]
                        formatted = formatted[:-len(ending)]
                    path.write_bytes(data.encode())
                    result = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr.decode())
                    self.assertEqual(result.stdout, formatted.encode())
                    self.assertEqual(path.read_bytes(), data.encode())
                    path.write_bytes(result.stdout)
                    again = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                    self.assertEqual(again.stdout, result.stdout)
            # Flat do actions must not accidentally become multiline statements.
            do_source = 'main : IO Unit\nmain = do\n  putStrLn (appendString "' + "a" * 110 + '" "b")\n'
            path.write_text(do_source)
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, do_source)
            literal = 'putStrLn "' + "x" * 140 + '"'
            path.write_text(literal)
            self.assertEqual(run("format", str(path)).stdout, literal)
            # Reformat a genuine project, then check/run the changed layout.
            original = ROOT / "examples/modules/records"
            for file in original.rglob("*.fib"):
                destination = Path(directory) / file.relative_to(original)
                destination.parent.mkdir(parents=True, exist_ok=True)
                text = subprocess.run([str(EXE), "format", str(file)], capture_output=True)
                self.assertEqual(text.returncode, 0, text.stderr.decode())
                destination.write_bytes(text.stdout)
            result = run("run", "--source-dir", directory, str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Records!\n")

    def test_conservative_source_formatting(self):
        with tempfile.TemporaryDirectory(prefix="format 'quoted' ") as directory:
            path = Path(directory) / "Main.fib"
            for ending in ("\n", "\r\n"):
                source = ('-- comment  spacing\t stays  \n'
                          'main:IO  Unit\nmain=putStrLn(appendString"🌍  e\u0301""!")  -- trailing  text  \n')
                expected = ('-- comment  spacing\t stays  \n'
                            'main : IO Unit\nmain = putStrLn (appendString "🌍  e\u0301" "!")  -- trailing  text  \n')
                original = source.replace("\n", ending).encode()
                path.write_bytes(original)
                result = run("format", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                # subprocess text mode normalizes CRLF, so inspect actual output bytes.
                raw = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                self.assertEqual(raw.stdout, expected.replace("\n", ending).encode())
                self.assertEqual(path.read_bytes(), original)
                report = json.loads(run("format", "--json", str(path)).stdout)
                self.assertEqual(report["original"].encode(), original)
                self.assertEqual(report["formatted"].encode(), raw.stdout)
                self.assertEqual(run("format", "--check", str(path)).returncode, 1)
                path.write_bytes(raw.stdout)
                canonical = path.read_bytes()
                again = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                self.assertEqual(again.stdout, canonical)
                result = run("format", "--check", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr, "")
            for source in ("", "-- only comment  ", "True", 'main : IO Unit\nmain = do\n\tputStrLn  "x"\n\tputStrLn "y"\n'):
                path.write_text(source)
                result = run("format", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                if source in ("", "-- only comment  ", "True"):
                    self.assertEqual(result.stdout, source)
                else:
                    self.assertIn('\n\tputStrLn "x"\n\tputStrLn "y"\n', result.stdout)
            # Formatting is syntax-only, not elaboration admission or checking.
            path.write_text('module Main\nrecord R:Type 0 where\n  constructor MkR\n'
                            '  eliminator useR\n  1 x:Bool\n  1 y:Bool\n  projection getX x\n'
                            'main:Bool\nmain="wrong"\n')
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("record R : Type 0 where", result.stdout)
            for content in (b"\xff", b"\xef\xbb\xbfTrue", b"main :", b"\x00"):
                path.write_bytes(content)
                result = run("format", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertEqual(path.read_bytes(), content)
            # Insertion of canonical spaces cannot evade the output cap.
            prefix = 'main:String\nmain="'
            content = prefix + "a" * (65536 - len(prefix) - 2) + '"\n'
            path.write_text(content)
            result = run("format", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("65536", result.stderr)

    def test_formatter_corpus_idempotence(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in sorted((ROOT / "examples/core").glob("*.fib")):
                result = run("format", str(path))
                # Every current core fixture should remain syntactically inspectable.
                self.assertEqual(result.returncode, 0, str(path) + result.stderr)
                formatted = target / path.name
                formatted.write_text(result.stdout)
                again = run("format", str(formatted))
                self.assertEqual(again.returncode, 0, again.stderr)
                self.assertEqual(again.stdout, result.stdout, str(path))
                self.assertEqual(run("check", str(path)).returncode,
                                 run("check", str(formatted)).returncode, str(path))

    def test_explicit_declaration_elaboration(self):
        result = run("elaborate", "examples/modules/record-projections/Data/Dictionary.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertFalse(report["checked"])
        self.assertEqual(report["representation"], "named-ir;not-source")
        self.assertEqual(report["module"], "Data.Dictionary")
        self.assertEqual([d["name"] for d in report["declarations"]],
                         ["Dictionary", "MkDictionary", "useDictionary", "getCombine", "getIdentity"])
        self.assertTrue(all(d["generated"] for d in report["declarations"]))
        self.assertIn("Sigma", report["declarations"][0]["value"])
        self.assertIn("pair-case", report["declarations"][2]["value"])
        source = (ROOT / "examples/modules/record-projections/Data/Dictionary.fib").read_text()
        for declaration in report["declarations"]:
            span = declaration["origin"]
            self.assertEqual(source[span["start"]["offset"]:span["end"]["offset"]], declaration["name"])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Main.fib"
            # Unresolved imports and ill-typed bodies are deliberately not accepted/checked here.
            entry.write_text('module Main\nimport Missing\nmain : Bool\nmain = "wrong"\n')
            result = run("elaborate", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            self.assertNotEqual(run("check", "--source-dir", str(root), str(entry)).returncode, 0)
            # Syntax remains inspectable, while declaration admission is a separate failure.
            unsafe = ('module Main\nrecord R : Type 0 where\n'
                      '  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 y : Bool\n'
                      '  projection getX x\nmain : IO Unit\nmain = putStrLn "never"\n')
            entry.write_text(unsafe)
            result = run("symbols", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("getX", [s["name"] for s in json.loads(result.stdout)["symbols"]])
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            result = run("elaborate", str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Elaboration", result.stderr)
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "elaboration")
            self.assertEqual(diagnostic["path"], str(entry.resolve()))
            self.assertEqual(diagnostic["position"]["line"], 7)

    def test_inferred_record_pattern_motives(self):
        example = ROOT / "examples/modules/pattern-inference/Main.fib"
        result = run("run", "--source-dir", str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Inferred patterns!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            source = example.read_text()
            path.write_text(source)
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Inferred patterns!\n")
            # Inferred matching still respects exact quantities and type annotations.
            for before, after in (
                ('(1 value : A) => value', '(1 value : A) => "discarded"'),
                ('(1 text : String) => if enabled then appendString text "!" else text',
                 '(1 text : String) => if enabled then appendString text text else text'),
                ('case box of (1 value : A)', 'case box of (value : A)'),
                ('case box of (1 value : A)', 'case box of (1 value : Bool)'),
                ('case box of (1 value : A) => value', 'case box of (1 _ : A) => "discarded"'),
                ('case message of (1 enabled : Bool) (1 text : String)',
                 'case message of (1 enabled : Bool) (1 enabled : String)'),
            ):
                path.write_text(source.replace(before, after))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, (before, after, result.stdout))
                self.assertEqual(result.stdout, "")
            # Inference preserves outer type parameters under a result's own Pi.
            closure = source.replace(
                "main : IO Unit",
                'constant : (0 A : Type 0) -> (1 box : Box A) -> (0 unused : A) -> A\n'
                'constant = \\(0 A : Type 0) => \\(1 box : Box A) => case box of (1 value : A) => \\(0 unused : A) => value\n'
                'main : IO Unit').replace(
                    'putStrLn (render (MkMessage True (recover String (MkBox String "Inferred patterns"))))',
                    'putStrLn (constant String (MkBox String "Closure!") "erased")')
            path.write_text(closure)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Closure!\n")
            path.write_text(source)
            lines = source.splitlines()
            line = next(i + 1 for i, text in enumerate(lines) if text.startswith("recover ="))
            column = lines[line - 1].rindex("value") + 1
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target = json.loads(result.stdout)["definition"]
            begin, end = target["range"]["start"]["offset"], target["range"]["end"]["offset"]
            self.assertEqual(source[begin:end], "value")
            self.assertLess(target["range"]["start"]["column"], column)
            # Stage-preserving runtime analysis must still reject erased extraction.
            path.write_text('module Main\nrecord R : Type 0 where\n'
                            '  constructor MkR\n  eliminator useR\n  0 value : String\n'
                            'main : IO Unit\nmain = putStrLn (case MkR "secret" of (0 value : String) => value)\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # Definitionally constant families are normalized only in result types.
            path.write_text(
                'module Main\n0 Constant : (0 flag : Bool) -> Type 0\n'
                'Constant = \\(0 flag : Bool) => String\n'
                'record R : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 flag : Bool\n'
                'main : IO Unit\nmain = putStrLn (case MkR True of (1 flag : Bool) => '
                '((if flag then "Constant!" else "other") : Constant flag))\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Constant!\n")
            # Canonical dependent unary motives now infer under result Pi binders.
            dependent = (ROOT / "examples/modules/singleton-records/Dependent.fib").read_text().replace(
                "module Dependent", "module Main")
            start = dependent.index("identityFor =")
            finish = dependent.index("\n\nmain :", start)
            implicit = ('identityFor = \\(1 tag : Tag) => case tag of (0 Item : Type 0) => '
                        '\\(1 x : Item) => x')
            path.write_text(dependent[:start] + implicit + dependent[finish:])
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent singleton!\n")
            # Named IR inspection preserves pending inference without claiming checked output.
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            self.assertIn("infer-record-case", str(inspected))
            explicit = ('identityFor = \\(1 tag : Tag) => case tag '
                        'return (\\(0 self : Tag) => ((1 x : itemType self) -> itemType self : Type 1)) '
                        'of (0 Item : Type 0) => \\(1 x : Item) => x')
            path.write_text(dependent[:start] + explicit + dependent[finish:])
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent singleton!\n")
            # Ordinary do bind/let contexts are propagated through result-header lowering.
            path.write_text(
                'module Main\nrecord R : Type 0 where\n  constructor MkR\n  eliminator useR\n  1 value : String\n'
                'main : IO Unit\nmain = do (Unit)\n'
                '  (1 text : String) <- pure String "Do context!"\n'
                '  let (1 box : R) = MkR text\n'
                '  putStrLn (case box of (1 value : String) => value)\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Do context!\n")

    def test_email_submission_state_model(self):
        example = ROOT / "examples/modules/email-service"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "sending\naccepted by relay\nsubmission unknown\ntransition rejected\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Delivery.fib").write_bytes((example / "Delivery.fib").read_bytes())
            outcomes = {("Queued", "Dispatch"): "sending",
                        ("Sending", "RelayAccepted"): "accepted by relay",
                        ("Sending", "AcknowledgementLost"): "submission unknown"}
            for state in ("Queued", "Sending", "AcceptedByRelay", "SubmissionUnknown"):
                for event in ("Dispatch", "RelayAccepted", "AcknowledgementLost"):
                    entry = root / "Main.fib"
                    entry.write_text(f'module Main\nimport Delivery\nmain : IO Unit\nmain = putStrLn (Delivery.transitionText (Delivery.advance Delivery.{state} Delivery.{event}))\n')
                    result = run("run", "--source-dir", str(root), str(entry))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stdout, outcomes.get((state, event), "transition rejected") + "\n")

    def test_source_nonrecursive_data_and_named_elimination(self):
        example = ROOT / "examples/modules/data"
        expected = "present\nmissing\ndependent package\n"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, expected)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for file in example.glob("*.fib"):
                destination = root / file.name
                destination.write_bytes(file.read_bytes())
                formatted = run("format", str(destination))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                destination.write_text(formatted.stdout)
                self.assertEqual(run("format", str(destination)).stdout, formatted.stdout)
            path = root / "Main.fib"
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, expected)
            source = path.read_text()
            inspected = run("elaborate", str(path))
            self.assertEqual(inspected.returncode, 0, inspected.stdout + inspected.stderr)
            ir = json.loads(inspected.stdout)
            self.assertFalse(ir["checked"])
            self.assertIn("nominal-type", str(ir))
            self.assertIn("variant-case", str(ir))
            lines = source.splitlines()
            line = next(i + 1 for i, text in enumerate(lines) if '(Just String "present")' in text)
            column = lines[line - 1].index("Just String") + 1
            target = run("definition", "--source-dir", str(root), "--entry", str(path), str(line), str(column), str(path))
            self.assertEqual(target.returncode, 0, target.stdout + target.stderr)
            point = json.loads(target.stdout)["definition"]["range"]
            self.assertEqual(source[point["start"]["offset"]:point["end"]["offset"]], "Just")
            # Header parameters and dependent constructor fields use actual authored binders.
            package = root / "Package.fib"
            text = package.read_text()
            line = next(i + 1 for i, value in enumerate(text.splitlines()) if 'Pack :' in value)
            column = text.splitlines()[line - 1].rindex("Item") + 1
            target = run("definition", "--source-dir", str(root), "--entry", str(path), str(line), str(column), str(package))
            self.assertEqual(target.returncode, 0, target.stdout + target.stderr)
            point = json.loads(target.stdout)["definition"]["range"]
            self.assertEqual(text[point["start"]["offset"]:point["end"]["offset"]], "Item")
            self.assertLess(point["start"]["offset"], text.index("(1 value : Item) -> Package"))
            # Private/unused generated data bodies still check before any output.
            package.write_text(text.replace("(1 value : Item) -> Package", "(1 value : Item) -> String"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            package.write_text(text)
            # No helper is generated unless requested; nominal/phantom identity remains checked.
            base = ('module Main\ndata Flag (0 A : Type 0) : Type 0 where\n'
                    '  MkFlag : Flag A\nmain : IO Unit\nmain = putStrLn "flags"\n')
            path.write_text(base)
            result = run("elaborate", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn("nominal-case", result.stdout)
            for bad in (
                base.replace('main : IO Unit', 'bad : Flag Bool\nbad = MkFlag String\nmain : IO Unit'),
                base.replace('main : IO Unit', 'data Other (0 A : Type 0) : Type 0 where\n  MkOther : Other A\nbad : Flag String\nbad = MkOther String\nmain : IO Unit'),
                base.replace('MkFlag : Flag A', 'MkFlag : Flag String'),
                base.replace('MkFlag : Flag A', 'MkFlag : (1 child : Flag A) -> Flag A'),
                base.replace('MkFlag : Flag A', 'MkFlag : (1 child : Main.Flag A) -> Flag A'),
                base.replace('MkFlag : Flag A', 'MkFlag : (1 child : Later) -> Flag A'),
                base.replace('(0 A : Type 0)', '(A : Type 0)'),
                base.replace('MkFlag : Flag A', 'MkFlag : (1 A : Bool) -> Flag A'),
                base.replace('MkFlag : Flag A', 'MkFlag : Flag A\n  MkFlag : Flag A'),
                base.replace('module Main\n', ''),
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, bad + result.stdout + result.stderr)
                self.assertEqual(result.stdout, "")
            # Ordinary helper arguments cannot pretend to share a linear capture.
            path.write_text('module Main\ndata Choice : Type 0 where\n  eliminator useChoice\n  Left : Choice\n  Right : Choice\nbad : (1 text : String) -> (1 choice : Choice) -> String\nbad = \\(1 text : String) => \\(1 choice : Choice) => useChoice (\\(0 self : Choice) => String) choice text text\nmain : IO Unit\nmain = putStrLn (bad "x" Left)\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # Nine parameters and sixteen alternatives are admitted by work budgets, not fixed caps.
            params = " ".join(f"(0 T{i} : Type 0)" for i in range(9))
            args = " ".join(f"T{i}" for i in range(9))
            wide = f"module Main\ndata Wide {params} : Type 0 where\n"
            wide += "".join(f"  Tag{i} : Wide {args}\n" for i in range(16))
            wide += 'main : IO Unit\nmain = putStrLn "wide"\n'
            path.write_text(wide)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "wide\n")
            # A wider constructor telescope uses existing dependent record packing.
            fields = " -> ".join(f"(1 value{i} : Bool)" for i in range(16))
            path.write_text(f'module Main\ndata Wide : Type 0 where\n  Pack : {fields} -> Wide\nmain : IO Unit\nmain = putStrLn "fields"\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_explicit_implementation_factories(self):
        example = ROOT / "examples/modules/implementation-factories"
        expected = "Hello, factories!\nReused Bool operations!\n"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, expected)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for file in example.rglob("*.fib"):
                destination = root / file.relative_to(example)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(file.read_bytes())
                formatted = run("format", str(destination))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                destination.write_text(formatted.stdout)
                self.assertEqual(run("format", str(destination)).stdout, formatted.stdout)
            path = root / "Main.fib"
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, expected)
            main = path.read_text()
            box = root / "BoxOps.fib"
            factory = box.read_text()
            # Explicit expression factories remain ordinary checked functions too.
            path.write_text(main.replace("BoxOps.boxedSemigroup String", "BoxOps.forwarded (BoxOps.Box String)").replace(
                "@{BoxOps.forwarded (BoxOps.Box String) @{implementation}}",
                "@{BoxOps.forwarded (BoxOps.Box String) @{BoxOps.boxedSemigroup String @{implementation}}}"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, expected)
            # Factories are never registered as closed global providers or recursively searched.
            path.write_text(main.replace("@{BoxOps.boxedSemigroup String @{implementation}}", "@{implementation}"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("No matching visible named implementation", result.stderr)
            self.assertEqual(result.stdout, "")
            path.write_text(main)
            # Header parameters scope over method bodies, with genuine definition targets.
            lines = factory.splitlines()
            line = next(i + 1 for i, text in enumerate(lines) if "MkBox A (" in text)
            column = lines[line - 1].index("MkBox A") + len("MkBox ") + 1
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(box))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            point = json.loads(result.stdout)["definition"]["range"]
            self.assertEqual(factory[point["start"]["offset"]:point["end"]["offset"]], "A")
            self.assertLess(point["start"]["line"], line)
            # Capturing a linear dictionary in an unrestricted method remains invalid.
            box.write_text(factory.replace("(ops : Algebra.Semigroup A)", "(1 ops : Algebra.Semigroup A)"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # Runtime non-dictionary inputs are not implementation factory parameters.
            box.write_text(factory.replace("(0 A : Type 0)", "(A : Type 0)"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            box.write_text(factory)
            # Local-schema elaboration exposes generated lambdas but does not certify them.
            local = ('module Local\ninterface C (0 A : Type 0) : Type 0 where\n'
                     '  constructor MkC\n  method : (1 value : A) -> A\n'
                     'implementation reuse : (0 A : Type 0) -> (ops : C A) => C A where\n'
                     '  method = \\(1 value : A) => method A @{ops} value\n'
                     'main : IO Unit\nmain = putStrLn "Local"\n')
            local_path = root / "Local.fib"
            local_path.write_text(local)
            result = run("check", "--source-dir", str(root), str(local_path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("elaborate", str(local_path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            for bad in (
                local.replace("(ops : C A) => C A", "(ops : String) -> C A").replace("method A @{ops} value", "value"),
                local.replace("(ops : C A) => C A", "(0 ops : C A) -> C A"),
                local.replace("method A @{ops} value", "True"),
                local.replace("method =", "missing ="),
                local.replace("where\n  method =", "where method ="),
            ):
                local_path.write_text(bad)
                self.assertNotEqual(run("check", "--source-dir", str(root), str(local_path)).returncode, 0)

    def test_named_infix_calls_preserve_application_semantics(self):
        example = ROOT / "examples/modules/infix"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            helpers = ('module Main\n'
                       'backwards : (1 left : String) -> (1 right : String) -> String\n'
                       'backwards = \\(1 left : String) => \\(1 right : String) => appendString right left\n'
                       'nand : (left : Bool) -> (right : Bool) -> Bool\n'
                       'nand = \\(left : Bool) => \\(right : Bool) => if left then if right then False else True else True\n')
            source = helpers + ('main : IO Unit\nmain = do\n'
                '  putStrLn ("a" `appendString` "b" `appendString` "c")\n'
                '  putStrLn ("a" `backwards` "b" `backwards` "c")\n'
                '  putStrLn (if True `nand` True `nand` False then "left" else "wrong")\n'
                '  putStrLn (if True `nand` (True `nand` False) then "wrong" else "right")\n'
                '  putStrLn (appendString "a" "b" `backwards` appendString "c" "d")\n'
                '  putStrLn ("a" `(if True `nand` False then appendString else backwards)` "b")\n'
                '  putStrLn ("tick`literal" `appendString` "!")\n')
            path.write_text(source)
            expected = "abc\ncba\nleft\nright\ncdab\nab\ntick`literal!\n"
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, expected)
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            self.assertIn("infix-apply", str(inspected))
            path.write_text(source.replace('`appendString`', '` appendString `'))
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn('"a" `appendString` "b"', formatted.stdout)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, expected)
            lines = formatted.stdout.splitlines()
            line = next(i + 1 for i, text in enumerate(lines) if '"a" `backwards`' in text)
            column = lines[line - 1].index("`backwards`") + 2
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            point = json.loads(result.stdout)["definition"]["range"]
            self.assertEqual(formatted.stdout[point["start"]["offset"]:point["end"]["offset"]], "backwards")
            long_source = helpers + 'main : IO Unit\nmain = putStrLn ("' + "a" * 55 + '" `appendString` "' + "b" * 55 + '")\n'
            path.write_text(long_source)
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn("\n", formatted.stdout[formatted.stdout.index('"aaaa'):])
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "a" * 55 + "b" * 55 + "\n")
            for bad in (
                helpers + '0 hidden : (1 a : String) -> (1 b : String) -> String\nhidden = appendString\nmain : IO Unit\nmain = putStrLn ("a" `hidden` "b")\n',
                helpers + 'duplicate : (1 text : String) -> String\nduplicate = \\(1 text : String) => text `appendString` text\nmain : IO Unit\nmain = putStrLn (duplicate "x")\n',
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            for expression in ('"a" `` "b"', '"a" `appendString "b"',
                               '"a" `appendString`', '"a" `True` "b"'):
                path.write_text(helpers + f"main : IO Unit\nmain = putStrLn ({expression})\n")
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            path.write_text(helpers + 'main : IO Unit\nmain = putStrLn (' + ' `appendString` '.join(['"x"'] * 300) + ')\n')
            result = run("check", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("budget", result.stderr.lower())
            local = 'putStrLn (let (op : (1 a : String) -> (1 b : String) -> String) = appendString in "a" `op` "b")\n'
            path.write_text(local)
            column = local.index("`op`") + 2
            result = run("rename-preview", "1", str(column), "join", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("join", result.stdout)

    def test_visible_named_implementation_selection(self):
        example = ROOT / "examples/modules/visible-implementations"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            base = ('module Main\ninterface C : Type 0 where\n  constructor MkC\n'
                    '  method : (1 text : String) -> String\n'
                    'implementation instance : C where\n  method = \\(1 text : String) => text\n'
                    'main : IO Unit\nmain = putStrLn (method @{implementation} "Visible!")\n')
            path.write_text(base)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Visible!\n")  # local and qualified aliases count once
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            self.assertIn("implementation-apply", str(inspected))
            formatted = run("format", str(path)).stdout
            self.assertIn("@{implementation}", formatted)
            path.write_text(formatted)
            self.assertEqual(run("format", str(path)).stdout, formatted)
            # Local-only requests do not silently change policy.
            path.write_text(base.replace("@{implementation}", "@{}"))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Ordinary same-shaped dictionary values are not implicit providers.
            ordinary = base.replace('implementation instance : C where\n  method = \\(1 text : String) => text',
                                    'instance : C\ninstance = MkC (\\(1 text : String) => text)')
            path.write_text(ordinary)
            result = run("check", "--json", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = next(d for d in json.loads(result.stdout)["diagnostics"] if d["stage"] == "elaboration")
            self.assertIn("No matching visible named implementation", diagnostic["message"])
            self.assertEqual(diagnostic["position"]["offset"], ordinary.index("@{implementation}"))
            path.write_text(ordinary.replace("@{implementation}", "@{instance}"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Visible!\n")
            extra = ('implementation second : C where\n'
                     '  method = \\(1 text : String) => appendString text "second"\n')
            ambiguous = base.replace("main : IO Unit", extra + "main : IO Unit")
            path.write_text(ambiguous)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Ambiguous visible named implementations", result.stderr)
            self.assertEqual(result.stdout, "")
            path.write_text(ambiguous.replace("@{implementation}", "@{instance}"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Visible!\n")
            same_value = base.replace("main : IO Unit", "implementation alias : C\nalias = instance\nmain : IO Unit")
            path.write_text(same_value)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Direct imports, not transitive reachability, grant provider visibility.
            library = root / "Library.fib"
            library_source = ('module Library\nexport\ninterface C : Type 0 where\n'
                              '  constructor MkC\n  method : (1 text : String) -> String\n'
                              'export\nimplementation instance : C where\n  method = \\(1 text : String) => text\n')
            library.write_text(library_source)
            (root / "Bridge.fib").write_text(
                'module Bridge\nimport Library\nexport\nuse : (dictionary : Library.C) -> String\n'
                'use = \\(dictionary : Library.C) => Library.method @{dictionary} "Imported!"\n')
            entry = 'module Main\nimport Bridge\nmain : IO Unit\nmain = putStrLn (Bridge.use @{implementation})\n'
            path.write_text(entry)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            path.write_text(entry.replace("import Bridge", "import Bridge\nimport Library"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Imported!\n")
            # A private implementation is checked but not offered to importers.
            library.write_text(library_source.replace("export\nimplementation", "implementation"))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Unused invalid providers cannot be filtered out to admit a program.
            library.write_text(library_source.replace('method = \\(1 text : String) => text', 'method = True'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_named_constraints_and_local_dictionary_selection(self):
        example = ROOT / "examples/modules/constraints"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            base = ('module Main\ninterface C : Type 0 where\n  constructor MkC\n'
                    '  method : (1 text : String) -> String\n'
                    'implementation instance : C where\n  method = \\(1 text : String) => text\n'
                    'apply : (ops : C) => (1 text : String) -> String\n'
                    'apply = \\(ops : C) => \\(1 text : String) => method @{} text\n'
                    'main : IO Unit\nmain = putStrLn (apply @{instance} "Local selection!")\n')
            path.write_text(base)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Local selection!\n")
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            self.assertIn("constraint-pi", str(inspected))
            self.assertIn("local-unique", str(inspected))
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn("@{}", formatted.stdout)
            self.assertIn("@{instance}", formatted.stdout)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            # A global implementation is never silently found by local search.
            missing = base.replace("apply @{instance}", "apply @{}")
            path.write_text(missing)
            result = run("check", "--json", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = next(d for d in json.loads(result.stdout)["diagnostics"] if d["stage"] == "elaboration")
            self.assertIn("No matching visible local", diagnostic["message"])
            self.assertEqual(diagnostic["position"]["offset"], missing.rindex("@{}"))
            # Two matching locals reject rather than selecting by order.
            ambiguous = base.replace('(ops : C) => (1 text', '(ops : C) => (other : C) => (1 text').replace(
                'apply = \\(ops : C) =>', 'apply = \\(ops : C) => \\(other : C) =>').replace(
                "apply @{instance}", "apply @{instance} @{instance}")
            path.write_text(ambiguous)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Ambiguous local dictionaries", result.stderr)
            self.assertEqual(result.stdout, "")
            path.write_text(ambiguous.replace("method @{}", "method @{ops}"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Local selection!\n")
            # Selection does not weaken a linear dictionary or revive erased locals.
            linear = base.replace('(ops : C)', '(1 ops : C)').replace(
                'method @{} text', 'appendString (method @{} text) (method @{} "twice")')
            path.write_text(linear)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            path.write_text(base.replace('(ops : C)', '(0 ops : C)'))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Ordinary erased dictionary binders are not eligible automatic candidates.
            path.write_text(base.replace('(ops : C) => (1 text', '(0 ops : C) -> (1 text').replace(
                '\\(ops : C) =>', '\\(0 ops : C) =>'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("No matching visible local", result.stderr)
            # Lexical shadowing hides an older candidate with the same name.
            path.write_text(base.replace("method @{} text", 'let (ops : Bool) = True in method @{} text'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("No matching visible local", result.stderr)
            for bad in (
                base.replace("(ops : C) => (1 text", "(ops : Bool) => (1 text"),
                base.replace("method @{} text", "method @{True} text"),
                base.replace("method @{} text", "appendString @{} text"),
                base.replace("method @{} text", "method @{ops text"),
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # Explicit selection references retain their real lexical target.
            explicit = base.replace("method @{} text", "method @{ops} text")
            path.write_text(explicit)
            lines = explicit.splitlines()
            line = next(i + 1 for i, text in enumerate(lines) if "method @{ops}" in text)
            column = lines[line - 1].index("@{ops}") + 3
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            point = json.loads(result.stdout)["definition"]["range"]
            self.assertEqual(explicit[point["start"]["offset"]:point["end"]["offset"]], "ops")
            # Imported graph formatted through syntax-only services still executes.
            for file in example.rglob("*.fib"):
                destination = root / file.relative_to(example)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(file.read_bytes())
                formatted = run("format", str(destination))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                destination.write_text(formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)

    def test_module_core_errors_have_declaration_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library = root / "ReqRes.fib"
            entry = root / "Main.fib"
            entry.write_text('module Main\nimport ReqRes\nmain : IO Unit\nmain = putStrLn "never"\n')
            invalid = ('module ReqRes\n\nrecord API : Type 0 where\n'
                       '  constructor MkAPI\n  0 req : Type 0\n  0 res : req -> Type 0\n')
            library.write_text(invalid)
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(str(library.resolve()) + ":3:8:", result.stderr)
            self.assertIn('generated declaration "API"', result.stderr)
            self.assertIn("declaration-level location", result.stderr)
            self.assertIn("inferred: Type1; expected: Type0", result.stderr)
            self.assertIn("record API : Type 0 where", result.stderr)
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "erased-checking")
            self.assertEqual(diagnostic["position"], {"offset": invalid.index("API"), "line": 3, "column": 8})
            self.assertEqual(diagnostic["path"], str(library.resolve()))
            # Runtime errors get the same honest declaration anchor.
            library.write_text('module ReqRes\n\nanswer : String\nanswer = True\n')
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(library.resolve()) + ":3:1:", result.stderr)
            self.assertIn('declaration "answer"', result.stderr)
            # Fixing the universe works; do not move the anchor to an invented field point.
            library.write_text(invalid.replace("API : Type 0", "API : Type 1"))
            self.assertEqual(run("check", "--source-dir", str(root), str(entry)).returncode, 0)

    def test_named_implementation_method_blocks(self):
        example = ROOT / "examples/modules/interface-blocks"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            base = ('module Main\ninterface C (0 A : Type 0) : Type 0 where\n'
                    '  constructor MkC\n  method : (1 x : A) -> A\n'
                    'implementation c : C String where\n'
                    '  method = \\(1 x : String) => x\n'
                    'main : IO Unit\nmain = putStrLn (method String c "Method block!")\n')
            path.write_text(base)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Method block!\n")
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            instance = next(d for d in inspected["declarations"] if d["name"] == "c")
            self.assertTrue(instance["implementation"])
            self.assertTrue(instance["generated"])
            self.assertIn("global[MkC]", instance["value"])
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            for bad in (
                base.replace('  method = \\(1 x : String) => x', '  missing = \\(1 x : String) => x'),
                base.replace('  method = \\(1 x : String) => x', '  method = True'),
                base.replace('  method = \\(1 x : String) => x', '  method = \\(1 x : String) => "discarded"'),
                base.replace('  method = \\(1 x : String) => x', '  method = \\(1 x : String) => x\n  method = \\(1 x : String) => x'),
                base.replace('implementation c : C String where', 'implementation c : C where'),
                base.replace('implementation c : C String where', 'implementation c : Unknown String where'),
                base.replace('  method = \\(1 x : String) => x', '  method ='),
                base.replace('  method = \\(1 x : String) => x', '  method = \\(x : String) => x'),
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, bad)
                self.assertEqual(result.stdout, "")
            # Multiline method expressions have their own indentation frame.
            path.write_text(base.replace(
                '  method = \\(1 x : String) => x',
                '  method = \\(1 x : String) =>\n    appendString\n      "Prefix: "\n      x'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Prefix: Method block!\n")
            long_body = ('  method = \\(1 input : String) => appendString '
                         '(appendString "This method deliberately has a lengthy readable prefix: " "continued: ") input')
            path.write_text(base.replace('  method = \\(1 x : String) => x', long_body))
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn('=>\n    ', formatted.stdout)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Missing methods report admission failure before typechecking a partial constructor.
            binary = ('module Main\ninterface C : Type 0 where\n'
                      '  constructor MkC\n  first : Bool\n  second : Bool\n'
                      'implementation c : C where\n  first = True\n'
                      'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(binary)
            result = run("check", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Missing implementation method second", result.stderr)
            # Blocks can use their own module qualifier but not future interface declarations.
            path.write_text(base.replace("implementation c : C String", "implementation c : Main.C String"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Method block!\n")
            header = base[:base.index("implementation c")]
            block = base[base.index("implementation c"):base.index("main : IO Unit")]
            path.write_text("module Main\n" + block + header.replace("module Main\n", "") +
                            'main : IO Unit\nmain = putStrLn "never"\n')
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Schema-guided mapping does not pretend ordinary record aliases are interfaces.
            path.write_text(base.replace("interface C", "record C").replace(
                'main = putStrLn (method String c "Method block!")', 'main = putStrLn "never"'))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # All imported source is formatted/executed through normal checking.
            for file in example.rglob("*.fib"):
                destination = root / file.relative_to(example)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(file.read_bytes())
                formatted = run("format", str(destination))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                destination.write_text(formatted.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            # Single-file inspection does not silently load imported schemas.
            result = run("elaborate", str(root / "Instances/Text.fib"))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("schema unavailable", result.stderr)
            # Reachability alone does not grant a transitive schema import.
            instance_path = root / "Instances/Text.fib"
            instance_source = instance_path.read_text()
            instance_path.write_text(instance_source.replace("import Algebra\n", ""))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            instance_path.write_text(instance_source)
            # Unused invalid dependency bodies prevent schema publication.
            algebra = root / "Algebra.fib"
            algebra_source = algebra.read_text()
            algebra.write_text(algebra_source + '\nbad : String\nbad = True\n')
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            algebra.write_text(algebra_source)
            # A private class publishes neither methods nor construction metadata.
            algebra = root / "Algebra.fib"
            algebra.write_text(algebra.read_text().replace("export\ninterface Semigroup", "interface Semigroup"))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)

    def test_erased_constructor_parameter_inference(self):
        example = ROOT / "examples/modules/pattern-inference/InferredParameters.fib"
        result = run("run", "--source-dir", str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Inferred parameters!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            pair = ('module Main\nrecord Both (0 A : Type 0) (0 B : Type 0) : Type 0 where\n'
                    '  constructor MkBoth\n  1 left : A\n  1 right : B\n'
                    'main : IO Unit\nmain = putStrLn (case MkBoth String Bool "Both" True of '
                    'MkBoth left right => if right then appendString left "!" else left)\n')
            path.write_text(pair)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Both!\n")
            formatted = run("format", str(path)).stdout
            path.write_text(formatted)
            self.assertEqual(run("format", str(path)).stdout, formatted)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Both!\n")
            # Typed field annotations remain an alternative; inference is still type-only.
            path.write_text(pair.replace("of MkBoth left right", "of MkBoth (1 left : String) (1 right : Bool)"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Both!\n")
            # Phantom parameters are not invented from unrelated binder annotations.
            phantom = ('module Main\nrecord Phantom (0 A : Type 0) : Type 0 where\n'
                       '  constructor MkPhantom\n  1 value : String\n'
                       'main : IO Unit\nmain = putStrLn (case MkPhantom Bool "Explicit phantom!" of MkPhantom value => value)\n')
            path.write_text(phantom)
            result = run("check", "--json", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertTrue(any(d["stage"] == "elaboration" and "supply them explicitly" in d["message"]
                                for d in json.loads(result.stdout)["diagnostics"]))
            path.write_text(phantom.replace("of MkPhantom value", "of (MkPhantom Bool) value"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Explicit phantom!\n")
            # No inversion of a computational type family.
            indexed = ('module Main\nrecord Indexed (0 flag : Bool) : Type 0 where\n'
                       '  constructor MkIndexed\n  1 value : if flag then String else Bool\n'
                       'main : IO Unit\nmain = putStrLn (case MkIndexed True "Explicit index!" of MkIndexed value => value)\n')
            path.write_text(indexed)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            path.write_text(indexed.replace("of MkIndexed value", "of (MkIndexed True) value"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Explicit index!\n")
            # Repeated constraints must agree, not silently choose the first occurrence.
            conflict = ('module Main\nrecord Same (0 A : Type 0) : Type 0 where\n'
                        '  constructor MkSame\n  1 first : A\n  1 second : A\n'
                        'record Mixed : Type 0 where\n  constructor MkMixed\n'
                        '  1 text : String\n  1 flag : Bool\n'
                        'main : IO Unit\nmain = putStrLn (case MkMixed "never" True of MkSame text flag => '
                        'if flag then appendString text "!" else text)\n')
            path.write_text(conflict)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # A solved parameter cannot capture a binder local to the matched type.
            escaping = ('module Main\nrecord Constant (0 A : Type 0) : Type 1 where\n'
                        '  constructor MkConstant\n  function : (0 X : Type 0) -> A\n'
                        'record Polymorphic : Type 1 where\n  constructor MkPolymorphic\n'
                        '  function : (0 X : Type 0) -> X\n'
                        'bad : (1 p : Polymorphic) -> String\n'
                        'bad = \\(1 p : Polymorphic) => case p of MkConstant function => "never"\n'
                        'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(escaping)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Inferred parameters do not normalize away an erased scrutinee demand.
            erased = ('module Main\nrecord Box (0 A : Type 0) : Type 0 where\n'
                      '  constructor MkBox\n  1 value : A\n'
                      '0 secret : Box String\nsecret = MkBox String "secret"\n'
                      'main : IO Unit\nmain = putStrLn (case secret of MkBox value => value)\n')
            path.write_text(erased)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # Qualified imported constructors need no separate inference registry.
            library = root / "Library.fib"
            library.write_text('module Library\nexport\nrecord Box (0 A : Type 0) : Type 0 where\n'
                               '  constructor MkBox\n  1 value : A\n')
            path.write_text('module Main\nimport Library\nmain : IO Unit\nmain = putStrLn '
                            '(case Library.MkBox String "Imported parameters!" of Library.MkBox value => value)\n')
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Imported parameters!\n")

    def test_inferred_constructor_field_binders(self):
        example = ROOT / "examples/modules/pattern-inference/InferredFields.fib"
        result = run("run", "--source-dir", str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Inferred payload!\nInferred family!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            source = example.read_text().replace("module InferredFields", "module Main")
            path.write_text(source)
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            self.assertIn("infer-field-binders", str(inspected))
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for old, new in (
                ("of MkPackage Item value => value", 'of MkPackage Item value => "discarded"'),
                ("of MkPackage Item value => value", "of MkPackage Item value => (\\(unused : Item) => value) value"),
                ("of MkPackage Item value", "of MkPackage Item Item"),
                ("of MkPackage Item value", "of MkPackage Item value extra"),
                ("of MkPackage Item value", "of MkPackage Item"),
                ("of MkPackage Item value", "of MkPackage Item _"),
            ):
                path.write_text(source.replace(old, new))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, (old, new))
                self.assertEqual(result.stdout, "")
            path.write_text(source.replace("  1 value : Item", "  0 value : Item"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # Unary parameters remain explicit; names infer both type and quantity.
            unary = ('module Main\nrecord Box (0 A : Type 0) : Type 0 where\n'
                     '  constructor MkBox\n  1 value : A\n'
                     'main : IO Unit\nmain = putStrLn (case MkBox String "Unary!" of (MkBox String) value => value)\n')
            path.write_text(unary)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Unary!\n")
            path.write_text(unary.replace("of (MkBox String) value", "of MkBox value"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Unary!\n")
            explicit = unary.replace('of (MkBox String)', 'return (\\(0 self : Box String) => String) of (MkBox String)')
            path.write_text(explicit)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Unary!\n")
            # Unrestricted field reuse is allowed, but linear wildcard discard is not.
            path.write_text(unary.replace("  1 value : A", "  value : A")
                            .replace("value => value)", "value => appendString value value)"))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Unary!Unary!\n")
            # Fresh inferred names remain selectable lexical binder targets.
            path.write_text(unary)
            line = 6
            column = unary.splitlines()[line - 1].rindex("value") + 1
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target = json.loads(result.stdout)["definition"]["range"]
            self.assertEqual(unary[target["start"]["offset"]:target["end"]["offset"]], "value")
            self.assertLess(target["start"]["column"], column)

    def test_constructor_named_record_patterns(self):
        example = ROOT / "examples/modules/pattern-inference/Named.fib"
        result = run("run", "--source-dir", str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Named patterns!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            source = example.read_text().replace("module Named", "module Main")
            path.write_text(source)
            inspected = json.loads(run("elaborate", str(path)).stdout)
            self.assertFalse(inspected["checked"])
            self.assertIn("constructor-record-case", str(inspected))
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Named patterns!\n")
            # Constructor and field variables resolve in different scopes.
            path.write_text(source)
            lines = source.splitlines()
            line = next(i + 1 for i, text in enumerate(lines) if text.startswith("unbox ="))
            column = lines[line - 1].index("MkBox A") + 1
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target = json.loads(result.stdout)["definition"]["range"]
            self.assertEqual(source[target["start"]["offset"]:target["end"]["offset"]], "MkBox")
            for bad in (
                source.replace("(MkBox A) (1 value : A)", "(MkBox Bool) (1 value : A)"),
                source.replace("of MkPackage", "of Missing"),
                source.replace("(MkBox A) (1 value : A)", "(MkBox A) (value : A)"),
                source.replace("(1 value : A) => value", "(1 value : A) => \"discarded\""),
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, bad)
                self.assertEqual(result.stdout, "")

            base = ('module Main\nrecord R : Type 0 where\n  constructor MkR\n  1 text : String\n'
                    'alias : (1 text : String) -> R\nalias = MkR\n'
                    'main : IO Unit\nmain = putStrLn (case MkR "Alias!" of alias (1 text : String) => text)\n')
            path.write_text(base)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Alias!\n")
            # A value-transforming packer is not a constructor pattern.
            path.write_text(base.replace("alias = MkR",
                                        'alias = \\(1 text : String) => MkR (appendString text "!")'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("transparently pack", result.stderr)
            self.assertEqual(result.stdout, "")
            # Structural compatibility is not nominal constructor discrimination.
            other = 'record S : Type 0 where\n  constructor MkS\n  1 other : String\n'
            path.write_text(base.replace("alias :", other + "alias :").replace(
                'of alias (1 text', 'of MkS (1 text'))
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Alias!\n")
            # Explicit motives remain available with constructor names.
            explicit = base.replace('of alias (1 text',
                                    'return (\\(0 self : R) => String) of alias (1 text')
            path.write_text(explicit)
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Alias!\n")
            # Local shadowing is respected: don't guess an unshadowed global constructor.
            path.write_text(base.replace("main : IO Unit",
                'bad : (MkR : (1 text : String) -> R) -> (1 r : R) -> String\n'
                'bad = \\(MkR : (1 text : String) -> R) => \\(1 r : R) => case r of MkR (1 text : String) => text\n'
                'main : IO Unit'))
            self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)
            # Cross-module qualified constructor prefixes use ordinary direct exports.
            library = root / "Library.fib"
            library.write_text('module Library\nexport\nrecord Box (0 A : Type 0) : Type 0 where\n'
                               '  constructor MkBox\n  1 value : A\n')
            path.write_text('module Main\nimport Library\nmain : IO Unit\nmain = putStrLn '
                            '(case Library.MkBox String "Imported!" of (Library.MkBox String) (1 value : String) => value)\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Imported!\n")
            library.write_text(library.read_text().replace("export\nrecord", "record"))
            self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)

    def test_optional_named_record_eliminators(self):
        example = ROOT / "examples/modules/pattern-inference/Minimal.fib"
        result = run("run", "--source-dir", str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "No named eliminator needed!\n")
        report = json.loads(run("elaborate", str(example)).stdout)
        names = [d["name"] for d in report["declarations"]]
        self.assertEqual(names, ["Message", "MkMessage", "Append", "MkAppend", "append",
                                 "textAppend", "render", "main"])
        self.assertFalse(any("$" in name for name in names))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            path.write_text(example.read_text().replace("module Minimal", "module Main"))
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout,
                             "No named eliminator needed!\n")
            # Direct typed matching handles binary records without named helpers too.
            source = ('module Main\nrecord Pair : Type 0 where\n  constructor MkPair\n'
                      '  1 left : String\n  1 right : String\n'
                      'main : IO Unit\nmain = putStrLn (case MkPair "Both " "fields!" of '
                      '(1 left : String) (1 right : String) => appendString left right)\n')
            path.write_text(source)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Both fields!\n")
            path.write_text(source.replace('appendString left right', 'left'))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Wider records with safe getters do not need a named consuming helper.
            path.write_text(
                'module Main\nrecord Flags : Type 0 where\n  constructor MkFlags\n'
                '  first : Bool\n  second : Bool\n  third : Bool\n  projection last third\n'
                'main : IO Unit\nmain = putStrLn (if last (MkFlags False False True) then "Wider!" else "bad")\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Wider!\n")
            # A requested helper is still emitted, checked and navigates to its token.
            explicit = source.replace("  constructor MkPair\n", "  constructor MkPair\n  eliminator usePair\n")
            path.write_text(explicit)
            names = [d["name"] for d in json.loads(run("elaborate", str(path)).stdout)["declarations"]]
            self.assertEqual(names[:3], ["Pair", "MkPair", "usePair"])
            # No dangling invented helper exists when the directive was absent.
            path.write_text(source.replace('main : IO Unit', 'bad : (1 p : Pair) -> String\n'
                                           'bad = \\(1 p : Pair) => usePair p\nmain : IO Unit'))
            self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)
            # Automatic methods navigate to authored tokens without a named eliminator.
            path.write_text(example.read_text().replace("module Minimal", "module Main"))
            text = path.read_text()
            lines = text.splitlines()
            line = next(i + 1 for i, value in enumerate(lines) if "append textAppend" in value)
            column = lines[line - 1].index("append textAppend") + 1
            result = run("definition", "--source-dir", str(root), "--entry", str(path),
                         str(line), str(column), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target = json.loads(result.stdout)["definition"]["range"]
            self.assertEqual(text[target["start"]["offset"]:target["end"]["offset"]], "append")
            # Dependent canonical motives do not rely on named helper functions.
            dependent = (ROOT / "examples/modules/pattern-inference/Dependent.fib").read_text()
            path.write_text("".join(line for line in dependent.replace("module Dependent", "module Main").splitlines(True)
                                    if not line.lstrip().startswith("eliminator ")))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent payload!\nDependent family!\n")
            # A whole imported graph can omit helpers without changing its behavior.
            original = ROOT / "examples/modules/interfaces"
            for file in original.rglob("*.fib"):
                destination = root / file.relative_to(original)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text("".join(line for line in file.read_text().splitlines(True)
                                               if not line.lstrip().startswith("eliminator ")))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")

    def test_dependent_motive_inference_and_budget(self):
        example = ROOT / "examples/modules/pattern-inference/Dependent.fib"
        result = run("run", "--source-dir", str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Dependent payload!\nDependent family!\n")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            source = example.read_text().replace("module Dependent", "module Main")
            path.write_text(source)
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            # Type-level projections do not permit runtime erased-field extraction.
            path.write_text(source.replace("  1 value : Item", "  0 value : Item").replace(
                "(1 value : Item)", "(0 value : Item)"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # Runtime use of the linear payload is still counted in the original branch.
            path.write_text(source.replace("(1 value : Item) => value",
                                           "(1 value : Item) => (\\(unused : Item) => value) value"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

            # Small source result type, large canonical dependent substitution.
            count = 60
            result_type = "".join(f"(0 x{i} : Item) -> " for i in range(count)) + "Bool"
            result_value = "".join(f"\\(0 x{i} : Item) => " for i in range(count)) + "True"
            header = (
                'module Main\nrecord Tag : Type 1 where\n  constructor MkTag\n'
                '  eliminator useTag\n  0 Item : Type 0\n'
                '0 functionType : (0 tag : Tag) -> Type 0\n'
                'functionType = \\(0 tag : Tag) => useTag (\\(0 self : Tag) => Type 0) tag '
                '(\\(0 Item : Type 0) => (' + result_type + '))\n'
                'choose : (1 tag : Tag) -> functionType tag\n')
            implicit = 'choose = \\(1 tag : Tag) => case tag of (0 Item : Type 0) => ' + result_value
            ending = '\nmain : IO Unit\nmain = putStrLn "Checked explicit motive!"\n'
            path.write_text(header + implicit + ending)
            result = run("check", "--json", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = next(d for d in json.loads(result.stdout)["diagnostics"] if d["stage"] == "elaboration")
            self.assertIn("dependent motive exceeds 512", diagnostic["message"])
            self.assertEqual(diagnostic["position"]["line"], 9)
            # Explicit user intent avoids that expanded canonical projection tree.
            explicit = ('choose = \\(1 tag : Tag) => case tag '
                        'return (\\(0 self : Tag) => functionType self) of (0 Item : Type 0) => ' + result_value)
            path.write_text(header + explicit + ending)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Checked explicit motive!\n")

    def test_explicit_interfaces_and_implementations(self):
        example = ROOT / "examples/modules/interfaces"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")
        report = json.loads(run("elaborate", str(example / "Algebra.fib")).stdout)
        self.assertFalse(report["checked"])
        self.assertEqual([d["name"] for d in report["declarations"][:4]],
                         ["Semigroup", "MkSemigroup", "useSemigroup", "combine"])
        self.assertTrue(all(d["generated"] for d in report["declarations"][:4]))
        inspected = json.loads(run("elaborate", str(example / "Instances/Text.fib")).stdout)
        self.assertTrue(all(d["implementation"] for d in inspected["declarations"]))
        # Definition targets are actual method tokens, not generated syntax.
        source = (example / "Algebra.fib").read_text()
        lines = source.splitlines()
        line = next(i + 1 for i, text in enumerate(lines) if "combine A dictionary" in text)
        column = lines[line - 1].index("combine A") + 1
        result = run("definition", "--source-dir", str(example), "--entry", str(example / "Main.fib"),
                     str(line), str(column), str(example / "Algebra.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        location = json.loads(result.stdout)["definition"]
        self.assertEqual(location["path"], str((example / "Algebra.fib").resolve()))
        begin, end = location["range"]["start"]["offset"], location["range"]["end"]["offset"]
        self.assertEqual(source[begin:end], "combine")
        self.assertEqual(location["range"]["start"]["line"],
                         next(i + 1 for i, text in enumerate(lines) if text.startswith("  combine :")))

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            base = (
                'module Main\ninterface Flag : Type 0 where\n'
                '  constructor MkFlag\n  eliminator useFlag\n  flag : Bool\n'
                'implementation first : Flag\nfirst = MkFlag True\n'
                'implementation second : Flag\nsecond = MkFlag False\n'
                'main : IO Unit\nmain = putStrLn (if flag second then "true" else "false")\n')
            path.write_text(base)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "false\n")  # No automatic instance selection.
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            for bad in (
                base.replace("second = MkFlag False", "second = MkFlag"),
                base.replace("second = MkFlag False", 'second = MkFlag "wrong"'),
                base.replace("  flag : Bool", "  1 flag : Bool"),
                base.replace("  flag : Bool", "  0 flag : Bool"),
                base.replace("  flag : Bool", "  flag : Bool\n  projection get flag"),
                base.replace("  flag : Bool", "  flag : Bool\n  flag : Bool"),
                base.replace("implementation second : Flag", "implementation 0 second : Flag"),
                base.replace("implementation second : Flag", "implementation first : Flag"),
                base.replace("module Main\n", ""),
                base.replace("implementation second", "implementation\nsecond"),
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, bad)
                self.assertEqual(result.stdout, "")
            # A named primitive alias is still not a structural dictionary.
            path.write_text('module Main\n0 Text : Type 0\nText = String\n'
                            'implementation wrong : Text\nwrong = "no"\n'
                            'main : IO Unit\nmain = putStrLn "never"\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("dictionary-shaped", result.stderr)
            self.assertEqual(result.stdout, "")
            # Introspection is expressly unchecked, even for this bad target.
            self.assertEqual(run("elaborate", str(path)).returncode, 0)
            # Quantities inside methods are invariant, not silently adapted.
            operation = (
                'module Main\ninterface Operation : Type 0 where\n'
                '  constructor MkOperation\n  eliminator useOperation\n'
                '  apply : (left : String) -> (right : String) -> String\n'
                'implementation operation : Operation\noperation = MkOperation appendString\n'
                'main : IO Unit\nmain = putStrLn (apply operation "explicit" " adapter")\n')
            path.write_text(operation)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            path.write_text(operation.replace(
                "implementation operation",
                'adapter : (left : String) -> (right : String) -> String\n'
                'adapter = \\(left : String) => \\(right : String) => appendString left right\n'
                'implementation operation').replace("operation = MkOperation appendString", "operation = MkOperation adapter"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "explicit adapter\n")
            # All unused implementations are checked before publication/output.
            path.write_text(base.replace("second = MkFlag False", 'second = MkFlag "bad"')
                            .replace("flag second", "flag first"))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Automatic method binders consume the normal declaration quota.
            fields = "".join(f"  method{i} : Bool\n" for i in range(62))
            path.write_text('module Main\ninterface TooMany : Type 0 where\n'
                            '  constructor MkTooMany\n  eliminator useTooMany\n' + fields)
            result = run("elaborate", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("budget", result.stderr)
            # Copy and format the actual imported example graph, then execute it.
            for original in example.rglob("*.fib"):
                destination = root / original.relative_to(example)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(original.read_bytes())
                formatted = run("format", str(destination))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                destination.write_text(formatted.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            # Private interface group members are not imported by guessing names.
            algebra = root / "Algebra.fib"
            algebra.write_text(algebra.read_text().replace("export\ninterface Semigroup", "interface Semigroup"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_singleton_records_and_dependent_elimination(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"

            def program(quantity, getter=True):
                return ('module Main\nrecord R : Type 0 where\n'
                        '  constructor MkR\n  eliminator useR\n'
                        '  ' + (quantity + ' ' if quantity else '') + 'value : String\n' +
                        ('  projection get value\n' if getter else '') +
                        'main : IO Unit\nmain = putStrLn (get (MkR "Singleton!"))\n')

            for quantity in ("1", ""):
                path.write_text(program(quantity))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "Singleton!\n")
                inspected = json.loads(run("elaborate", str(path)).stdout)
                self.assertFalse(inspected["checked"])
                formatted = run("format", str(path)).stdout
                path.write_text(formatted)
                self.assertEqual(run("format", str(path)).stdout, formatted)
            path.write_text(program("0"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Erased fields", result.stderr + result.stdout)
            self.assertEqual(result.stdout, "")
            path.write_text(program("0", False).replace(
                'putStrLn (get (MkR "Singleton!"))',
                'useR (\\(0 self : R) => IO Unit) (MkR "erased") (\\(0 value : String) => putStrLn "Erased!")'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Erased!\n")
            # Erased IO descriptions stored in a singleton never execute.
            path.write_text(
                'module Main\nrecord Actions : Type 0 where\n'
                '  constructor MkActions\n  eliminator useActions\n  0 action : IO Unit\n'
                'main : IO Unit\nmain = useActions (\\(0 self : Actions) => IO Unit) '
                '(MkActions (putStrLn "never")) (\\(0 action : IO Unit) => putStrLn "Only!")\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Only!\n")
            # An arbitrary dependent motive inspects an erased wrapped type.
            path.write_text(
                'module Main\nrecord Tag : Type 1 where\n'
                '  constructor MkTag\n  eliminator useTag\n  0 Item : Type 0\n'
                '0 itemType : (0 tag : Tag) -> Type 0\n'
                'itemType = \\(0 tag : Tag) => useTag (\\(0 self : Tag) => Type 0) tag (\\(0 Item : Type 0) => Item)\n'
                'identityFor : (1 tag : Tag) -> (1 x : itemType tag) -> itemType tag\n'
                'identityFor = \\(1 tag : Tag) => useTag (\\(0 self : Tag) => ((1 x : itemType self) -> itemType self : Type 1)) tag (\\(0 Item : Type 0) => \\(1 x : Item) => x)\n'
                'main : IO Unit\nmain = putStrLn (identityFor (MkTag String) "Dependent singleton!")\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent singleton!\n")
            # Quantity-aware unary wrappers are not their naked payloads.
            path.write_text(program("1").replace('get (MkR "Singleton!")', 'MkR "Singleton!"'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            compatible = ('record S : Type 0 where\n  constructor MkS\n'
                          '  eliminator useS\n  1 other : String\n')
            source = program("1").replace("main : IO Unit", compatible + "main : IO Unit").replace(
                'get (MkR "Singleton!")', 'get (MkS "Singleton!")')
            path.write_text(source)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Singleton!\n")
            path.write_text(source.replace("  1 other : String", "  other : String"))
            self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)
            for body in ('"dropped"', 'appendString (get record) (get record)'):
                path.write_text(program("1").replace(
                    'main : IO Unit', 'bad : (1 record : R) -> String\n'
                    'bad = \\(1 record : R) => ' + body + '\nmain : IO Unit'))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_wider_dependent_records(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"

            def program(fields, requests="", body='putStrLn "unused"'):
                return ('module Main\nrecord R : Type 1 where\n'
                        '  constructor MkR\n  eliminator useR\n' +
                        "".join("  " + field + "\n" for field in fields) + requests +
                        'main : IO Unit\nmain = ' + body + '\n')

            # Third-field type depends on two distinct erased predecessors.
            fields = ["0 Item : Type 0", "0 flag : Bool",
                      "1 value : if flag then Item else Bool"]
            path.write_text(program(fields, "  projection get value\n",
                                    'putStrLn (get (MkR String True "Dependent!"))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent!\n")
            # Dependent motive observes the complete reconstructed record.
            path.write_text(
                program(fields, "  projection get value\n", 'putStrLn (recover (MkR String True "Motive!"))')
                .replace('main : IO Unit',
                         '0 valueType : (0 r : R) -> Type 0\n'
                         'valueType = \\(0 r : R) => useR (\\(0 self : R) => Type 0) r '
                         '(\\(0 Item : Type 0) => \\(0 flag : Bool) => \\(1 value : if flag then Item else Bool) => if flag then Item else Bool)\n'
                         'recover : (1 r : R) -> valueType r\n'
                         'recover = \\(1 r : R) => useR (\\(0 self : R) => (valueType self : Type 1)) r '
                         '(\\(0 Item : Type 0) => \\(0 flag : Bool) => \\(1 value : if flag then Item else Bool) => value)\n'
                         'main : IO Unit'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Motive!\n")

            # Sparse transitive type dependencies in an eight-field telescope.
            fields = ["0 A : Type 0", "0 Family : (0 x : A) -> Type 0", "0 x : A",
                      "0 witness : Family x", "0 flag : Bool", "0 unused0 : Unit",
                      "0 unused1 : Unit", "1 value : Family x"]
            path.write_text(program(fields, "  projection get value\n",
                'putStrLn (get (MkR Unit (\\(0 x : Unit) => String) () "witness" True () () "Sparse!"))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Sparse!\n")
            # Late payload mismatches still reject before any effects.
            path.write_text(program(fields, "  projection get value\n",
                'putStrLn (get (MkR Unit (\\(0 x : Unit) => String) () "witness" True () () False))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

            # Every width, including eight fields, consumes every linear field.
            for width in list(range(2, 10)) + [12, 16]:
                names = [f"field{i}" for i in range(width)]
                fields = [f"1 {name} : String" for name in names]
                combine = names[-1]
                for name in reversed(names[:-1]):
                    combine = f"appendString {name} ({combine})"
                args = " ".join(f'"{i}"' for i in range(width))
                path.write_text(program(fields, body=f'useR (\\(0 self : R) => (IO Unit : Type 1)) (MkR {args}) '
                                        f'(\\(1 {names[0]} : String) => ' +
                                        "".join(f"\\(1 {name} : String) => " for name in names[1:]) +
                                        f'putStrLn ({combine}))'))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "".join(map(str, range(width))) + "\n")
                # No linear field may vanish in the generated branch.
                path.write_text(program(fields, body=f'useR (\\(0 self : R) => (IO Unit : Type 1)) (MkR {args}) '
                                        '(' + "".join(f"\\(1 {name} : String) => " for name in names) +
                                        f'putStrLn {names[0]})'))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

            # Erased extraction traverses past field eight; no fixed fuel of 8.
            fields = [f"0 tag{i} : Bool" for i in range(9)] + ["0 Item : Type 0", "1 value : Item"]
            path.write_text(program(fields, "  projection get value\n",
                                    'putStrLn (get (MkR True True True True True True True True True String "Long path!"))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Long path!\n")

            # More than eight getter requests are ordinary declaration slots.
            # All nine independent getters remain within construction bounds.
            fields = [f"field{i} : Bool" for i in range(9)]
            requests = "".join(f"  projection get{i} field{i}\n" for i in range(9))
            path.write_text(program(fields, requests,
                                    'putStrLn (if get8 (MkR True True True True True True True True True) then "Getters!" else "bad")'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Getters!\n")
            # Same normalized telescope, different record/field names: structural.
            compatible = (
                'record S : Type 1 where\n  constructor MkS\n  eliminator useS\n' +
                "".join(f"  other{i} : Bool\n" for i in range(9)))
            path.write_text(program(fields, requests,
                                    'putStrLn (if get8 (MkS True True True True True True True True True) then "Structural!" else "bad")')
                            .replace("main : IO Unit", compatible + "main : IO Unit"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Structural!\n")
            for bad_fields in ([],
                               ["first : Bool", "second : Bool", "first : String"]):
                path.write_text(program(bad_fields))
                self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)
            # A getter must reject a discarded linear field anywhere in the tail.
            fields = ["0 Item : Type 0", "0 flag : Bool", "1 kept : String", "1 lost : String"]
            path.write_text(program(fields, "  projection get kept\n"))
            result = run("check", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("linear", result.stderr + result.stdout)

    def test_record_construction_admission_not_field_cap(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"

            def record(name, width):
                return (f"record {name} : Type 0 where\n  constructor Mk{name}\n  eliminator use{name}\n" +
                        "".join(f"  field{i} : Bool\n" for i in range(width)))

            # Syntax-only tools retain an oversized telescope without expanding it.
            source = "module Main\n" + record("R", 200) + 'main : IO Unit\nmain = putStrLn "never"\n'
            path.write_text(source)
            self.assertEqual(run("symbols", str(path)).returncode, 0)
            self.assertEqual(run("format", str(path)).returncode, 0)
            result = run("check", "--json", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertTrue(any(d["stage"] == "elaboration" and
                                "construction budget exhausted" in d["message"]
                                for d in report["diagnostics"]))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # The construction allowance is cumulative, not reset for each record.
            path.write_text("module Main\n" + "".join(record(f"R{i}", 32) for i in range(7)) +
                            "main : Bool\nmain = True\n")
            result = run("elaborate", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("construction budget exhausted", result.stdout + result.stderr)

    def test_safe_record_projections(self):
        root = "examples/modules/record-projections"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Safe projections!\n")
        result = run("eval", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Safe projections!")', result.stdout)
        with tempfile.TemporaryDirectory(prefix="projections ") as directory:
            target = Path(directory)
            entry = target / "Main.fib"
            def program(first, second, requests, body, result_type="IO Unit"):
                return ('module Main\nrecord R : Type 0 where\n'
                        '  constructor MkR\n  eliminator useR\n'
                        f'  {first}\n  {second}\n' +
                        "".join(f"  projection {name} {field}\n" for name, field in requests) +
                        f'main : {result_type}\nmain = {body}\n')
            # Both positions, all permitted discard/selection quantity combinations.
            for left in ("0 left : Bool", "1 left : Bool", "left : Bool"):
                for right in ("0 right : Bool", "1 right : Bool", "right : Bool"):
                    for selected in ("left", "right"):
                        selected_decl = left if selected == "left" else right
                        other_decl = right if selected == "left" else left
                        allowed = not selected_decl.startswith("0 ") and not other_decl.startswith("1 ")
                        entry.write_text(program(left, right, [("get", selected)],
                                                 'putStrLn (if get (MkR True False) then "true" else "false")'))
                        result = run("run", "--source-dir", str(target), str(entry))
                        if allowed:
                            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                            self.assertEqual(result.stdout, "true\n" if selected == "left" else "false\n")
                        else:
                            self.assertNotEqual(result.returncode, 0)
                            self.assertEqual(result.stdout, "")
            # A getter consumes its record, even when its fields are reusable.
            entry.write_text(program("left : Bool", "right : Bool",
                                     [("getLeft", "left"), ("getRight", "right")],
                                     'putStrLn "never"').replace(
                'main : IO Unit',
                'bad : (1 record : R) -> Bool\n'
                'bad = \\(1 record : R) => andBool (getLeft record) (getRight record)\n'
                'main : IO Unit'))
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # The second result type genuinely depends on an erased first field.
            entry.write_text(program(
                "0 flag : Bool", "1 value : if flag then String else Bool", [("getValue", "value")],
                'putStrLn (getValue (MkR True "dependent"))'))
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "dependent\n")
            for requests in ([("get", "missing")], [("get", "left"), ("get", "right")],
                             [(f"get{i}", "left") for i in range(61)]):
                entry.write_text(program("left : Bool", "right : Bool", requests, 'putStrLn "never"'))
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # Dependent parameterized second-field projection, across a module boundary.
            library = target / "Library.fib"
            library_source = ('module Library\nexport\nrecord Box (0 A : Type 0) : Type 0 where\n'
                              '  constructor MkBox\n  eliminator useBox\n'
                              '  0 tag : Unit\n  1 value : A\n  projection payload value\n')
            library.write_text(library_source)
            entry.write_text('module Main\nimport Library\nmain : IO Unit\n'
                             'main = putStrLn (Library.payload String (Library.MkBox String () "imported"))\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "imported\n")
            source = entry.read_text()
            offset = source.index("payload")
            point = source[:offset].rsplit("\n", 1)[-1]
            result = run("definition", "--source-dir", str(target), "--entry", str(entry),
                         "4", str(len(point) + 1), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            location = json.loads(result.stdout)["definition"]
            self.assertEqual(location["path"], str(library.resolve()))
            self.assertEqual(library_source[location["range"]["start"]["offset"]:
                                            location["range"]["end"]["offset"]], "payload")
            library.write_text(library_source.replace("export\nrecord", "record"))
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Unbound name", result.stderr)

    def test_consuming_record_patterns(self):
        root = "examples/modules/records"
        result = run("run", "--source-dir", root, root + "/Patterns.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Patterns!\n")
        result = run("eval", "--source-dir", root, root + "/Patterns.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Patterns!")', result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            header = "module Main\nimport Data.Message\nmain : IO Unit\nmain = putStrLn "
            prefix = ('(case Data.Message.MkMessage True "payload" return '
                      '(\\(0 self : Data.Message.Message) => String) of ')
            failures = [
                '(1 loud : Bool) (1 text : String) => text)',
                '(1 loud : Bool) (1 text : String) => if loud then appendString text text else text)',
                '(loud : Bool) (text : String) => if loud then text else text)',
                '(1 _ : Bool) (1 text : String) => text)',
                '(1 loud : Bool) (1 text : Bool) => if loud then "wrong" else "wrong")',
                '(1 same : Bool) (1 same : String) => same)',
                '(1 loud : Bool) => "missing")',
                '(1 loud : Bool) (1 text : String) (1 extra : Unit) => text)',
            ]
            for body in failures:
                entry.write_text(header + prefix + body + "\n")
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0, body)
                self.assertEqual(result.stdout, "")
            # Erased wildcards are allowed; linear wildcards above cannot discard.
            entry.write_text(
                'module Main\nrecord Marked : Type 0 where\n  constructor MkMarked\n'
                '  eliminator useMarked\n  0 mark : Unit\n  1 value : String\n'
                'main : IO Unit\nmain = putStrLn (case MkMarked () "wildcard" return '
                '(\\(0 self : Marked) => String) of (0 _ : Unit) (1 value : String) => value)\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "wildcard\n")
            # Motive is outside pattern scope, not re-resolved after binding.
            entry.write_text(header + '(case Data.Message.MkMessage True "x" return missing of '
                             '(1 missing : Bool) (1 text : String) => if missing then text else text)\n')
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unbound name "missing"', result.stderr)
            # Shared lexical traversal identifies authored pattern binders, not synthetic spans.
            source = ('case unknown return (\\(0 self : Unknown) => String) of\n'
                      '  (0 A : Type 0) (1 value : A) => value\n')
            entry.write_text(source)
            offset = source.rindex("value")
            line = source[:offset].count("\n") + 1
            column = len(source[:offset].rsplit("\n", 1)[-1]) + 1
            result = run("definition", str(line), str(column), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            span = json.loads(result.stdout)["definition"]
            self.assertEqual(span["start"]["offset"], source.index("value :"))
            domain = source.index("A) =>")
            result = run("definition", "2", str(len(source[:domain].rsplit("\n", 1)[-1]) + 1), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            span = json.loads(result.stdout)["definition"]
            self.assertEqual(span["start"]["offset"], source.index("A :"))
            # Rename is lexical only and preserves the pattern scopes.
            result = run("rename-preview", str(line), str(column), "payload", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(len(json.loads(result.stdout)["edits"]), 2)

    def test_record_parameter_telescopes(self):
        root = "examples/modules/record-parameters"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Record parameters!\n")
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            # Value indices, not only Type parameters; branch types specialize.
            flagged = ('module Main\nrecord Flagged (0 flag : Bool) : Type 0 where\n'
                       '  constructor MkFlagged\n  eliminator useFlagged\n'
                       '  0 tag : Unit\n  1 payload : if flag then String else Bool\n')
            entry.write_text(flagged + 'main : IO Unit\nmain = putStrLn '
                             '(useFlagged True (\\(0 self : Flagged True) => String) '
                             '(MkFlagged True () "indexed") (\\(0 tag : Unit) => \\(1 payload : String) => payload))\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "indexed\n")
            bad_programs = [
                flagged + 'main : Flagged False\nmain = MkFlagged False () "wrong"\n',
                flagged + 'bad : (0 flag : Bool) -> Bool\n'
                'bad = \\(0 flag : Bool) => flag\nmain : IO Unit\nmain = putStrLn "never"\n',
                'module Main\nrecord R (0 B : A) (0 A : Type 0) : Type 0 where\n'
                '  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 y : Bool\n'
                'main : IO Unit\nmain = putStrLn "never"\n',
                'module Main\nimport Data.AppendDictionary\nmain : IO Unit\n'
                'main = putStrLn (Data.AppendDictionary.appendWith String '
                '(Data.AppendDictionary.MkAppendDictionary String appendString "") "a" "b")\n',
                'module Main\nimport Data.Indexed\nmain : IO Unit\n'
                'main = putStrLn (Data.Indexed.MkIndexed True True True "bad")\n',
            ]
            for source in bad_programs:
                entry.write_text(source)
                result = run("check", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # Parameters can equal global declaration names without capture.
            entry.write_text(
                'module Main\nrecord Capture (0 Capture : Type 0) (0 MkCapture : Type 0) : Type 0 where\n'
                '  constructor MkCapture\n  eliminator useCapture\n'
                '  1 left : Capture\n  1 right : MkCapture\n'
                'main : Capture String Bool\nmain = MkCapture String Bool "left" True\n')
            result = run("eval", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('"left"', result.stdout)
            # A reusable dictionary works at Bool too; methods/identity are data.
            entry.write_text(
                'module Main\nimport Data.AppendDictionary\n'
                'both : (left : Bool) -> (right : Bool) -> Bool\n'
                'both = \\(left : Bool) => \\(right : Bool) => andBool left right\n'
                'main : IO Unit\nmain = putStrLn (if Data.AppendDictionary.appendWith Bool '
                '(Data.AppendDictionary.MkAppendDictionary Bool both True) True False then "wrong" else "bool")\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "bool\n")

    def test_named_dependent_records(self):
        root = "examples/modules/records"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Records!\n")
        result = run("eval", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Records!")', result.stdout)
        entry_text = (ROOT / root / "Main.fib").read_text()
        point = entry_text.index("MkMessage")
        line = entry_text[:point].count("\n") + 1
        column = len(entry_text[:point].rsplit("\n", 1)[-1]) + 1
        result = run("definition", "--source-dir", root, "--entry", root + "/Main.fib",
                     str(line), str(column), root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        definition = json.loads(result.stdout)["definition"]
        self.assertEqual(definition["path"], str((ROOT / root / "Data/Message.fib").resolve()))
        message_text = (ROOT / root / "Data/Message.fib").read_text()
        self.assertEqual(message_text[definition["range"]["start"]["offset"]:
                                      definition["range"]["end"]["offset"]], "MkMessage")
        with tempfile.TemporaryDirectory(prefix="records ") as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            message = target / "Data/Message.fib"
            package = target / "Data/Package.fib"
            original_message = message.read_text()
            original_package = package.read_text()
            header = "module Main\nimport Data.Package\nimport Data.Message\nmain : IO Unit\nmain = "
            for body in (
                'putStrLn (Data.Package.recover (Data.Package.MkPackage Bool "wrong"))',
                'putStrLn (Data.Message.render (Data.Message.MkMessage True True))',
                'putStrLn (Data.Message.consumeMessage (\\(0 self : Data.Message.Message) => String) '
                '(Data.Message.MkMessage True "text") (\\(1 loud : Bool) => \\(1 text : String) => text))',
                'putStrLn (Data.Message.consumeMessage (\\(0 self : Data.Message.Message) => String) '
                '(Data.Message.MkMessage True "text") (\\(loud : Bool) => \\(text : String) => text))',
                'putStrLn (Data.Package.unpackPackage (\\(0 self : Data.Package.Package) => (String : Type 1)) '
                '(Data.Package.MkPackage Bool True) (\\(0 Item : Type 0) => \\(1 value : Item) => value))',
            ):
                entry.write_text(header + body + "\n")
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            entry.write_bytes((ROOT / root / "Main.fib").read_bytes())
            message.write_text(original_message.replace("export\nrecord", "record"))
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unbound name", result.stderr)
            message.write_text(original_message)
            # Constructor and record names can coincide with field names without capture.
            package.write_text(
                "module Data.Package\nexport\nrecord Package : Type 1 where\n"
                "  constructor MkPackage\n  eliminator unpackPackage\n"
                "  0 Package : Type 0\n  1 MkPackage : Package\n")
            entry.write_text('module Main\nimport Data.Package\nmain : IO Unit\n'
                             'main = putStrLn (Data.Package.unpackPackage '
                             '(\\(0 self : Data.Package.Package) => (String : Type 1)) '
                             '(Data.Package.MkPackage String "ok") '
                             '(\\(0 A : Type 0) => \\(1 value : A) => '
                             'case () of () => "bad"))\n')
            # This branch drops a linear payload; name-collision lowering itself checks.
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            entry.write_text('module Main\nimport Data.Package\n'
                             'main : Data.Package.Package\nmain = Data.Package.MkPackage String "ok"\n')
            result = run("eval", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('"ok"', result.stdout)
            package.write_text(original_package.replace("record Package : Type 1", "record Package : Type 0"))
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            package.write_text(original_package)
            # Reachable dependencies are checked, including unused record definitions.
            entry.write_bytes((ROOT / root / "Main.fib").read_bytes())
            for replacement in (
                original_message + "\nrecord Unused : Type 0 where\n  constructor MkUnused\n  eliminator useUnused\n  1 x : Bool\n  1 y : missing\n",
                original_message.replace("1 text : String", "1 text : missing"),
                original_message.replace("  1 text : String", "  1 text : String\n  1 extra : Bool"),
                original_message.replace("  1 text : String", "  1 loud : String"),
                original_message.replace("  eliminator consumeMessage", "eliminator consumeMessage"),
            ):
                message.write_text(replacement)
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

            # Initial named records are transparent structural abbreviations.
            entry.write_text(
                'module Main\nrecord First : Type 0 where\n  constructor MkFirst\n'
                '  eliminator useFirst\n  1 flag : Bool\n  1 text : String\n'
                'record Second : Type 0 where\n  constructor MkSecond\n'
                '  eliminator useSecond\n  1 other : Bool\n  1 value : String\n'
                'main : Second\nmain = MkFirst True "structural"\n')
            result = run("eval", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('"structural"', result.stdout)

    def test_staged_erased_module_globals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library = root / "Types.fib"
            entry = root / "Main.fib"
            source = ('module Types\nexport\n0 Bit : Type 0\nBit = Bool\n'
                      'export\n0 Alias : Type 0\nAlias = Types.Bit\n'
                      'export\n0 secret : Bool\nsecret = True\n'
                      'export\n0 text : String\ntext = "hidden"\n'
                      'export\n0 Choose : (0 bit : Bool) -> Type 0\n'
                      'Choose = \\(0 bit : Bool) => if bit then String else Bool\n')
            library.write_text(source, encoding="utf-8")
            entry.write_text(
                'module Main\nimport Types\nvalue : Types.Alias\nvalue = True\n'
                'identity : (0 A : Type 0) -> (1 x : A) -> A\n'
                'identity = \\(0 A : Type 0) => \\(1 x : A) => x\n'
                'message : Types.Choose True\nmessage = "staged"\n'
                'other : Types.Choose False\nother = True\n'
                'main : IO Unit\nmain = putStrLn (if identity Types.Alias value then message else "wrong")\n',
                encoding="utf-8")
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "staged\n")
            # Erased data may be passed to an erased parameter.
            entry.write_text(
                'module Main\nimport Types\nignore : (0 bit : Bool) -> String\n'
                'ignore = \\(0 bit : Bool) => "ignored"\n'
                'main : IO Unit\nmain = putStrLn (ignore Types.secret)\n', encoding="utf-8")
            self.assertEqual(run("run", "--source-dir", str(root), str(entry)).stdout, "ignored\n")
            for body in ('putStrLn Types.text', 'putStrLn (if Types.secret then "leak" else "")',
                         'bind Bool Unit (pure Bool Types.secret) (\\(1 bit : Bool) => putStrLn (if bit then "leak" else ""))'):
                entry.write_text('module Main\nimport Types\nmain : IO Unit\nmain = ' + body + '\n',
                                 encoding="utf-8")
                for command in ("check", "eval", "run"):
                    result = run(command, "--source-dir", str(root), str(entry))
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertEqual(result.stdout, "")
            entry.write_text('module Main\nimport Types\nmain : IO Unit\nmain = putStrLn "safe"\n',
                             encoding="utf-8")
            library.write_text(source + '0 broken : Bool\nbroken = "wrong"\n', encoding="utf-8")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            self.assertEqual(report["diagnostics"][0]["stage"], "erased-checking")
            self.assertEqual(report["diagnostics"][0]["path"], str(library.resolve()))
            self.assertIsNotNone(report["diagnostics"][0]["position"])
            self.assertIn("declaration-level location", report["diagnostics"][0]["message"])
            library.write_text(source, encoding="utf-8")
            # Headerless local typed-let opacity has not changed.
            entry.write_text('import Types\nmain : IO Unit\nmain = putStrLn Types.text\n', encoding="utf-8")
            self.assertNotEqual(run("run", "--source-dir", str(root), str(entry)).returncode, 0)
            entry.write_text('module Main\n0 main : Bool\nmain = True\n', encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("main must be unrestricted", result.stderr)

    def test_explicit_generic_operation_profiles(self):
        root = "examples/modules/operations"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\n")
        result = run("eval", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Hello, Fibril!")', result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            failures = [
                ('module Main\nimport Algebra.Operation\nmain : IO Unit\n'
                 'main = putStrLn (Algebra.Operation.combineThree String appendString "a" "b" "c")\n'),
                ('module Main\nimport Algebra.Operation\nimport Instances.Text\n'
                 'bad : (1 text : String) -> String\n'
                 'bad = \\(1 text : String) => Algebra.Operation.combineThree String Instances.Text.append text "" ""\n'
                 'main : IO Unit\nmain = putStrLn "must not execute"\n'),
                ('module Main\nAlias : Type 0\nAlias = String\n'
                 'main : IO Unit\nmain = putStrLn "must not execute"\n'),
                ('module Main\n0 secret : String\nsecret = "must not execute"\n'
                 'main : IO Unit\nmain = putStrLn secret\n'),
            ]
            for source in failures:
                entry.write_text(source, encoding="utf-8")
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # An operation profile alone does not enforce associativity.
            entry.write_text(
                'module Main\nimport Algebra.Operation\n'
                'nand : (left : Bool) -> (right : Bool) -> Bool\n'
                'nand = \\(left : Bool) => \\(right : Bool) => notBool (andBool left right)\n'
                'main : IO Unit\n'
                'main = putStrLn (if Algebra.Operation.combineThree Bool nand True True False then "shape only" else "unexpected")\n',
                encoding="utf-8")
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "shape only\n")

    def test_builtin_and_prelude_references(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Reference.fib"
            def reference(source, token, skip=0):
                path.write_text(source, encoding="utf-8")
                offset = source.index(token) + skip
                line = source[:offset].count("\n") + 1
                column = len(source[:offset].rsplit("\n", 1)[-1]) + 1
                result = run("reference", str(line), str(column), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                return json.loads(result.stdout)["reference"]
            for name in ("String", "Unit", "Bool", "Type"):
                target = reference(name + (" 0" if name == "Type" else ""), name)
                self.assertEqual(target["kind"], "builtin-documentation")
                self.assertEqual(target["name"], name)
                self.assertNotIn("range", target)
            target = reference("IO Unit", "IO")
            self.assertEqual(target["kind"], "builtin-documentation")
            self.assertIn("Compiler primitive", " ".join(target["lines"]))
            for name in ("putStrLn", "pure", "bind", "map", "appendString"):
                target = reference(name, name)
                self.assertEqual(target["kind"], "bundled-prelude-source")
                source = target["source"]
                start = target["range"]["start"]["offset"]
                end = target["range"]["end"]["offset"]
                self.assertEqual(source[start:end], name)
                self.assertTrue(source[end:].startswith(" ="))
                self.assertEqual(source, (ROOT / "stdlib/Prelude.fib").read_text())
            for source, token, skip in [
                ('"String IO putStrLn"', "IO", 0),
                ("-- IO\nTrue", "IO", 0),
                ("\\(1 IO : String) => IO", "=> IO", 3),
                ("putStrLn : String\nputStrLn = \"local\"\nmain : String\nmain = putStrLn",
                 "main = putStrLn", 7),
                ("Text.putStrLn", "putStrLn", 0),
            ]:
                self.assertIsNone(reference(source, token, skip))

    def test_checked_project_definition_queries(self):
        for ending in ("\n", "\r\n"):
            with self.subTest(ending=ending), tempfile.TemporaryDirectory(prefix="definitions 'quoted' ") as directory:
                root = Path(directory)
                (root / "Text").mkdir()
                entry = root / "Main.fib"
                library = root / "Text/Greeting.fib"
                shared = root / "Shared.fib"
                sources = {
                    entry: ('-- 🌍e\u0301\nmodule Main\nimport Text.Greeting\nmain : IO Unit\n'
                            'main = let (1 Text : String) = "local" in (Text.Greeting.greet) Text\n'),
                    library: ('module Text.Greeting\nimport Shared\n'
                              'helper : (1 value : String) -> String\n'
                              'helper = \\(1 value : String) => appendString "prefix" value\n'
                              'export\ngreet : (1 text : String) -> IO Unit\n'
                              'greet = \\(1 text : String) => putStrLn (Text.Greeting.helper (appendString Shared.message text))\n'),
                    shared: 'module Shared\nexport\nmessage : String\nmessage = "shared"\n',
                }
                sources = {path: text.replace("\n", ending) for path, text in sources.items()}
                for path, text in sources.items():
                    path.write_bytes(text.encode("utf-8"))

                def point(text, offset):
                    return {"offset": offset, "line": text[:offset].count("\n") + 1,
                            "column": len(text[:offset].rsplit("\n", 1)[-1]) + 1}

                def query(path, text, token, skip=0):
                    position = point(text, text.index(token) + skip)
                    result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                                 str(position["line"]), str(position["column"]), str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stderr, "")
                    report = json.loads(result.stdout)
                    self.assertEqual(report["version"], 2)
                    self.assertTrue(report["checked"])
                    self.assertEqual(report["query"], str(path.resolve()))
                    self.assertEqual({s["path"]: s["text"] for s in report["sources"]},
                                     {str(p.resolve()): t for p, t in sources.items()})
                    return report["definition"]

                def expect(target, path, token):
                    self.assertEqual(target["path"], str(path.resolve()))
                    start = sources[path].index(token)
                    self.assertEqual(target["range"]["start"], point(sources[path], start))
                    name = token.split()[0]
                    self.assertEqual(target["range"]["end"], point(sources[path], start + len(name)))

                expect(query(entry, sources[entry], "Text.Greeting.greet", len("Text.Greeting.")),
                       library, "greet =")
                # Query a library without inventing its own main.
                expect(query(library, sources[library], "Text.Greeting.helper", len("Text.Greeting.")),
                       library, "helper =")
                expect(query(library, sources[library], "Shared.message", len("Shared.")),
                       shared, "message =")
                # The local Text binder does not capture the qualified namespace.
                local = query(entry, sources[entry], ") Text", 2)
                self.assertEqual(local["path"], str(entry.resolve()))
                self.assertEqual(local["range"]["start"],
                                 point(sources[entry], sources[entry].index("Text :")))
                for token, skip in (("Text.Greeting.greet", 0), ("Text.Greeting.greet", len("Text")),
                                    ('"local"', 1), ("import Text", 7)):
                    self.assertIsNone(query(entry, sources[entry], token, skip))
                self.assertIsNone(query(library, sources[library], "putStrLn"))
                outside = root / "Unreachable.fib"
                outside.write_text("module Unreachable\n", encoding="utf-8")
                result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                             "1", "1", str(outside))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("not in the checked project graph", result.stderr)
                for replacement in ("Text.Greeting.helper", "Shared.message"):
                    entry.write_text("module Main\nimport Text.Greeting\nmain : String\nmain = " +
                                     replacement + "\n", encoding="utf-8")
                    result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                                 "4", "8", str(entry))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                entry.write_bytes(sources[entry].encode("utf-8"))
                # No successful navigation packet is emitted for an invalid unused body.
                shared.write_text('module Shared\nexport\nmessage : String\nmessage = "shared"\n'
                                  'unused : Bool\nunused = "wrong"\n', encoding="utf-8")
                result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                             "1", "1", str(library))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(str(shared.resolve()), result.stderr)

    def test_project_json_source_provenance(self):
        with tempfile.TemporaryDirectory(prefix="project json ") as directory:
            root = Path(directory)
            entry = root / "Main.fib"
            dependency = root / "Library.fib"
            entry_source = ('module Main\nimport Library\nmain : IO Unit\n'
                            'main = Library.output\n')
            dependency_source = ('-- 🌍\r\nmodule Library\r\nexport\r\noutput : IO Unit\r\n'
                                 'output = putStrLn "not executed"\r\n')
            entry.write_text(entry_source, encoding="utf-8")
            dependency.write_bytes(dependency_source.encode("utf-8"))
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = json.loads(result.stdout)
            self.assertEqual(report["version"], 2)
            self.assertTrue(report["accepted"])
            self.assertEqual(report["entry"], str(entry.resolve()))
            self.assertEqual(report["root"], str(root.resolve()))
            self.assertEqual(report["diagnostics"], [])
            self.assertEqual({s["path"]: s["text"] for s in report["sources"]}, {
                str(entry.resolve()): entry_source, str(dependency.resolve()): dependency_source})
            self.assertNotIn("\nnot executed\n", result.stdout)
            self.assertEqual(result.stderr, "")
            # A dependency resolver point must never become an entry-file point.
            bad = '-- 🌍\r\nmodule Library\r\nexport\r\noutput : IO Unit\r\noutput = missing\r\n'
            dependency.write_bytes(bad.encode("utf-8"))
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["path"], str(dependency.resolve()))
            self.assertEqual(diagnostic["stage"], "resolution")
            self.assertTrue(diagnostic["sourceAvailable"])
            self.assertEqual(diagnostic["position"], {
                "offset": bad.index("missing"), "line": 5, "column": 10})
            self.assertEqual({s["path"]: s["text"] for s in report["sources"]}[diagnostic["path"]], bad)
            dependency.write_text('module Library\nexport\noutput : IO Unit\noutput = True\n', encoding="utf-8")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["path"], str(dependency.resolve()))
            self.assertEqual(diagnostic["stage"], "runtime-checking")
            self.assertEqual(diagnostic["position"], {"offset": len("module Library\nexport\n"), "line": 3, "column": 1})
            self.assertIn("declaration-level location", diagnostic["message"])
            self.assertIsNone(diagnostic["byteOffset"])
            self.assertTrue(diagnostic["sourceAvailable"])
            dependency.write_bytes("🌍".encode("utf-8") + b"\xff")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "decoding")
            self.assertEqual(diagnostic["path"], str(dependency.resolve()))
            self.assertEqual(diagnostic["byteOffset"], 4)
            self.assertIsNone(diagnostic["position"])
            self.assertFalse(diagnostic["sourceAvailable"])
            self.assertEqual(report["sources"], [])
            dependency.write_text("\u202e", encoding="utf-8")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "source-validation")
            self.assertEqual(diagnostic["position"], {"offset": 0, "line": 1, "column": 1})
            self.assertFalse(diagnostic["sourceAvailable"])
            dependency.unlink()
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["path"], str(entry.resolve()))
            self.assertEqual(diagnostic["position"]["line"], 2)
            self.assertTrue(diagnostic["sourceAvailable"])
            self.assertEqual(len(report["sources"]), 1)
            # Known empty text is not the same as an unavailable source snapshot.
            entry.write_bytes(b"")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            self.assertEqual(report["sources"], [{"path": str(entry.resolve()), "text": ""}])
            self.assertTrue(report["diagnostics"][0]["sourceAvailable"])

    def test_module_execution_and_evaluation(self):
        root = "examples/modules/checked"
        entry = root + "/Main.fib"
        result = run("run", "--source-dir", root, entry)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\n")
        self.assertEqual(result.stderr, "")
        result = run("eval", "--source-dir", root, entry)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Hello, Fibril!")', result.stdout)
        self.assertNotIn("\nHello, Fibril!\n", result.stdout)
        result = run("eval", "--source-dir", root, "--fuel", "0", entry)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("budget exhausted", result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            dependency = root / "Library.fib"
            entry = root / "Main.fib"
            dependency.write_text(
                "module Library\nexport\nidentity : (0 A : Type 0) -> (1 x : A) -> A\n"
                "identity = \\(0 A : Type 0) => \\(1 x : A) => x\n",
                encoding="utf-8")
            entry.write_text(
                'module Main\nimport Library\nmain : String\n'
                'main = Library.identity String "pure result"\n', encoding="utf-8")
            result = run("eval", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: "pure result"', result.stdout)
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("IO Unit", result.stderr)
            # A later invalid plan is fully prepared before any writes.
            body = ('module Main\nimport Library\nmain : IO Unit\nmain = do\n'
                    '  putStrLn "must not print"\n')
            entry.write_text(body + '  putStrLn True\n', encoding="utf-8")
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # A bad unused dependency definition also prevents all output.
            dependency.write_text(
                "module Library\nunused : Bool\nunused = \"wrong\"\n", encoding="utf-8")
            entry.write_text('module Main\nimport Library\nmain : IO Unit\n'
                             'main = putStrLn "must not print"\n', encoding="utf-8")
            for command in ("eval", "run"):
                result = run(command, "--source-dir", str(root), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(str(dependency.resolve()) + ":2:1:", result.stderr)
                self.assertIn("declaration-level location", result.stderr)
            dependency.write_text("module Library\n", encoding="utf-8")
            # Runtime action cap remains separate from successful project checking.
            entry.write_text(
                'module Main\nimport Library\ntwice : IO Unit\ntwice = do\n'
                '  putStrLn "never"\n  putStrLn "never"\n'
                'main : IO Unit\nmain = do\n' + '  twice\n' * 33, encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("output action count limit", result.stderr)
            for fuel in ("-1", "4097", "x"):
                result = run("eval", "--source-dir", str(root), "--fuel", fuel, str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("Fuel", result.stderr)

    def test_checked_module_interfaces(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def module(name, imports=(), body=""):
                path = root.joinpath(*name.split(".")).with_suffix(".fib")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("module " + name + "\n" +
                                "".join("import " + value + "\n" for value in imports) + body,
                                encoding="utf-8")
                return path
            library = module("Text.Greeting", body=(
                'hidden : String\nhidden = "private"\n'
                'export\ngreet : (1 text : String) -> IO Unit\n'
                'greet = \\(1 text : String) => putStrLn (appendString hidden text)\n'
                'export\nidentity : (0 A : Type 0) -> (1 x : A) -> A\n'
                'identity = \\(0 A : Type 0) => \\(1 x : A) => x\n'))
            entry = module("Main", ("Text.Greeting",), (
                'main : IO Unit\nmain = Text.Greeting.greet '
                '(Text.Greeting.identity String " must not print")\n'))
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Type: (IO Unit)", result.stdout)
            self.assertNotIn("must not print", result.stdout)
            self.assertEqual(result.stderr, "")
            module("Main", ("Text.Greeting",),
                   'main : IO Unit\nmain = do (Unit)\n'
                   '  let (1 original : String) = "block"\n'
                   '  (1 text : String) <- pure String (Text.Greeting.identity String original)\n'
                   '  Text.Greeting.greet (text : String)\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            entry = module("Main", ("Text.Greeting",),
                           'main : String\nmain = Text.Greeting.hidden\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Unbound name", result.stderr)
            self.assertIn(str(entry.resolve()), result.stderr)
            # Transitive modules are not implicitly visible.
            module("Bridge", ("Text.Greeting",), 'export\nvalue : Bool\nvalue = True\n')
            module("Main", ("Bridge",), 'main : Bool\nmain = Text.Greeting.identity Bool True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unbound name", result.stderr)
            # Equal leaf names remain distinct qualified exports.
            module("First", body='export\nvalue : Bool\nvalue = True\n')
            module("Second", body='export\nvalue : String\nvalue = "second"\n')
            module("Main", ("First", "Second"),
                   'main : String\nmain = if First.value then Second.value else "no"\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Type: String", result.stdout)
            # Earlier private definitions may use the current module's qualifier.
            module("First", body='private : Bool\nprivate = True\nexport\nvalue : Bool\nvalue = First.private\n')
            self.assertEqual(run("check", "--source-dir", str(root), str(entry)).returncode, 0)
            # Invalid private definitions fail before any interface is published.
            library = module("First", body='unused : Bool\nunused = "bad"\nexport\nvalue : Bool\nvalue = True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(library.resolve()), result.stderr)
            self.assertIn("declaration-level location", result.stderr)  # actual declaration, not an invented subterm point
            module("First", body='1 secret : Bool\nsecret = True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unrestricted", result.stderr)
            module("Main", (), 'other : Bool\nother = True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("own main", result.stderr)
            # Anonymous entry keeps existing local-let/quantity semantics.
            entry.write_text('main : Bool\nmain = True\n', encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            entry.write_text("0 Bit : Type 0\nBit = Bool\nmain : Bit\nmain = True\n", encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)

    def test_module_expansion_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "M0.fib").write_text(
                "module M0\nexport\nf : Bool -> Bool\nf = \\(x : Bool) => x\n", encoding="utf-8")
            for index in range(1, 16):
                (root / f"M{index}.fib").write_text(
                    f"module M{index}\nimport M{index - 1}\nexport\nf : Bool -> Bool\n"
                    f"f = \\(x : Bool) => andBool (M{index - 1}.f x) (M{index - 1}.f x)\n",
                    encoding="utf-8")
            entry = root / "Main.fib"
            entry.write_text("module Main\nimport M15\nmain : Bool\nmain = M15.f True\n", encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Expanded core construction budget", result.stderr)

    def test_qualified_reference_syntax(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Library.fib").write_text(
                "module Library\nexport\nvalue : String\nvalue = \"data\"\n", encoding="utf-8")
            entry = root / "Main.fib"
            entry.write_text(
                "module Main\nimport Library\nmain : String\nmain = Library.value\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            result = run("symbols", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("definition", "4", "8", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIsNone(json.loads(result.stdout)["definition"])
            result = run("check", str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Module checking requires --source-dir", result.stdout)
            entry.write_text("Library.value\n", encoding="utf-8")
            result = run("check", "--json", str(entry))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "resolution")
            self.assertIn("Library.value", diagnostic["message"])
            self.assertEqual(diagnostic["position"]["column"], 1)

    def test_module_graph_discovery(self):
        with tempfile.TemporaryDirectory(prefix="fibril graph ") as directory:
            base = Path(directory)
            root = base / "source '🌍'"
            root.mkdir()
            def module(name, imports=(), body=""):
                path = root.joinpath(*name.split(".")).with_suffix(".fib")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("module " + name + "\n" +
                                "".join("import " + value + "\n" for value in imports) + body,
                                encoding="utf-8")
                return path
            shared = module("Shared", body='value : String\nvalue = "🌍"\n')
            module("Left", ("Shared",))
            module("Right", ("Shared",))
            entry = module("Main", ("Left", "Right"),
                           'main : IO Unit\nmain = putStrLn "must not execute"\n')
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            graph = json.loads(result.stdout)
            self.assertFalse(graph["checked"])
            self.assertEqual(graph["root"], str(root.resolve()))
            self.assertEqual([n["module"] for n in graph["modules"]], ["Shared", "Left", "Right", "Main"])
            self.assertEqual(graph["modules"][0]["bytes"], len(shared.read_bytes()))
            self.assertNotIn("must not execute", result.stdout)
            self.assertEqual(result.stderr, "")
            # No kernel admission: syntactically valid, ill-typed modules can be inspected.
            module("Shared", body="value : Bool\nvalue = missing\n")
            self.assertEqual(run("module-graph", str(root), str(entry)).returncode, 0)
            module("Shared", ("Main",))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Import cycle", result.stderr)
            module("Shared")
            module("Main", ("Absent",))
            result = run("module-graph", str(root), str(entry))
            self.assertIn(f"{entry.resolve()}:2:1:", result.stderr)
            self.assertIn("exact-case", result.stderr)
            self.assertEqual(result.stdout, "")
            module("Main", ("Wrong",))
            wrong = module("Wrong")
            wrong.write_text("module Different\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertIn(str(wrong.resolve()), result.stderr)
            self.assertIn("does not match", result.stderr)
            wrong.write_text("value : Bool\nvalue = True\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertIn("require a module header", result.stderr)
            # Canonical aliases must not claim a second logical module name.
            wrong.unlink()
            wrong.symlink_to(shared)
            module("Main", ("Shared", "Wrong"))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("does not match", result.stderr)
            # Check case using directory entries, even on case-insensitive filesystems.
            case = module("Case")
            case.rename(root / "case.fib")
            module("Main", ("Case",))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("exact-case", result.stderr)
            outside = base / "outside.fib"
            outside.write_text("module Escape\n", encoding="utf-8")
            (root / "Escape.fib").symlink_to(outside)
            module("Main", ("Escape",))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("escapes canonical source root", result.stderr)
            self.assertEqual(result.stdout, "")
            result = run("module-graph", str(root), str(outside))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Entry escapes", result.stderr)
            # Named entries must map back to their canonical file.
            entry.write_text("module Unrelated\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            # Anonymous legacy entries remain inspectable, but not importable.
            entry.write_text("True\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIsNone(json.loads(result.stdout)["modules"][0]["module"])

    def test_module_graph_budgets(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Main.fib"
            for count, accepted in ((31, True), (32, False)):
                for index in range(count):
                    (root / f"M{index}.fib").write_text(f"module M{index}\n", encoding="utf-8")
                entry.write_text("module Main\n" +
                                 "".join(f"import M{i}\n" for i in range(count)), encoding="utf-8")
                result = run("module-graph", str(root), str(entry))
                self.assertEqual(result.returncode == 0, accepted, result.stdout + result.stderr)
                if not accepted:
                    self.assertEqual(result.stdout, "")
                    self.assertIn("count budget", result.stderr)
            entry.write_text("module Main\n" + "".join(f"import M{i}\n" for i in range(9)), encoding="utf-8")
            for index in range(9):
                header = f"module M{index}\n--"
                (root / f"M{index}.fib").write_text(header + "a" * (65536 - len(header)), encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Aggregate", result.stderr)
            self.assertEqual(result.stdout, "")

    def test_module_document_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "metadata.fib"
            source = ("-- 🌍\r\nmodule Text.Greeting\r\nimport Data.String\r\n"
                      "hidden : String\r\nhidden = \"data\"\r\n"
                      "export\r\nvalue : String\r\nvalue = hidden\r\n")
            path.write_bytes(source.encode("utf-8"))
            result = run("symbols", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            symbols = json.loads(result.stdout)["symbols"]
            self.assertEqual([s["name"] for s in symbols], ["hidden", "value"])
            self.assertEqual([s["exported"] for s in symbols], [False, True])
            self.assertEqual(symbols[1]["range"]["start"]["line"], 6)
            self.assertEqual(symbols[1]["selection"]["start"]["line"], 7)
            for symbol in symbols:
                span = symbol["selection"]
                self.assertEqual(source[span["start"]["offset"]:span["end"]["offset"]], symbol["name"])
            result = run("definition", "8", "9", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target = json.loads(result.stdout)["definition"]
            self.assertEqual(target["start"]["line"], 5)
            result = run("rename-preview", "8", "9", "renamed", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("project-aware", result.stderr)
            for args in (("check",), ("eval",), ("run",)):
                result = run(*args, str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Module checking requires --source-dir", result.stdout + result.stderr)
            result = run("check", "--json", str(path))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["position"]["line"], 2)
            for source in (
                "module A\nimport B\nimport B\n",
                "module A\nmodule B\n",
                "module A\nimport b\n",
                "module A\nvalue : Bool\nvalue = True\nimport B\n",
                "module A\nexport value : Bool\nvalue = True\n",
                "export\nmain : Bool\nmain = True\n",
                "module A\nexport\n",
            ):
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("symbols", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")

    def test_json_check_reports(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "checking.fib"
            for source in ("True", 'main : IO Unit\nmain = putStrLn "never printed"\n'):
                path.write_text(source, encoding="utf-8")
                result = run("check", "--json", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                report = json.loads(result.stdout)
                self.assertEqual(report["version"], 1)
                self.assertTrue(report["accepted"])
                self.assertEqual(report["diagnostics"], [])
                self.assertTrue(report["report"])
                self.assertNotIn("never printed", result.stdout)
                self.assertEqual(result.stderr, "")
            for source, stage, located in (
                ("missing", "resolution", True),
                ("\\(1 x : Bool) =>", "parsing", True),
                ("@", "lexing", True),
                ("(True : String)", "runtime-checking", False),
                ('(\\(1 x : String) => "discard") "input"', "runtime-checking", False),
            ):
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("check", "--json", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stderr, "")
                    report = json.loads(result.stdout)
                    self.assertFalse(report["accepted"])
                    self.assertEqual(report["report"], [])
                    diagnostic = report["diagnostics"][0]
                    self.assertEqual(diagnostic["stage"], stage)
                    self.assertEqual(diagnostic["severity"], "error")
                    self.assertEqual(diagnostic["position"] is not None, located)
                    self.assertIsNone(diagnostic["byteOffset"])
            source = '-- 🌍\r\nmain : String\r\nmain = missing\r\n'
            path.write_bytes(source.encode("utf-8"))
            result = run("check", "--json", str(path))
            point = json.loads(result.stdout)["diagnostics"][0]["position"]
            self.assertEqual(point, {"offset": source.index("missing"), "line": 3, "column": 8})
            for raw, byte_offset in ((b"\xff", 0), ("🌍".encode("utf-8") + b"\xff", 4)):
                path.write_bytes(raw)
                result = run("check", "--json", str(path))
                diagnostic = json.loads(result.stdout)["diagnostics"][0]
                self.assertEqual(diagnostic["stage"], "decoding")
                self.assertIsNone(diagnostic["position"])
                self.assertEqual(diagnostic["byteOffset"], byte_offset)
            path.write_text('"🌍"\n\u202e', encoding="utf-8")
            result = run("check", "--json", str(path))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "source-validation")
            self.assertEqual(diagnostic["position"], {"offset": 4, "line": 2, "column": 1})
            self.assertIsNone(diagnostic["byteOffset"])
            path.unlink()
            result = run("check", "--json", str(path))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "loading")
            self.assertIsNone(diagnostic["position"])
            self.assertEqual(result.stderr, "")

    def test_boolean_library(self):
        result = run("run", "examples/core/boolean-library.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Allowed.\nDenied.\nFallback enabled.\n")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "boolean-library.fib"
            for left in (False, True):
                expression = "notBool " + str(left)
                path.write_text("main : Bool\nmain = " + expression + "\n", encoding="utf-8")
                result = run("eval", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("Normal: " + str(not left), result.stdout)
                for right in (False, True):
                    for operation, expected in (("andBool", left and right), ("orBool", left or right)):
                        expression = f"{operation} {left} {right}"
                        path.write_text("main : Bool\nmain = " + expression + "\n", encoding="utf-8")
                        result = run("eval", str(path))
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertIn("Normal: " + str(expected), result.stdout)
            path.write_text(
                'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
                '  if andBool False () then putStrLn "yes" else putStrLn "no"\n',
                encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_pure_string_equality(self):
        result = run("run", "examples/core/string-equal.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\nHello, guest!\n")
        result = run("check", "examples/core/string-equal.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, Fibril!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "equal.fib"
            for expression, expected in (
                ('equalString "" ""', "True"),
                ('equalString "λ 🌍" "λ 🌍"', "True"),
                ('equalString "é" "é"', "False"),
                ('equalString "Fibril" "fibril"', "False"),
            ):
                path.write_text("main : Bool\nmain = " + expression + "\n", encoding="utf-8")
                result = run("eval", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("Normal: " + expected, result.stdout)
            path.write_text(
                'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
                '  if (\\(1 x : String) => equalString x x) "same" then putStrLn "yes" else putStrLn "no"\n',
                encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_pure_string_append(self):
        result = run("run", "examples/core/string-append.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\n")
        result = run("check", "examples/core/string-append.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, Fibril!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "append.fib"
            path.write_text('main : String\nmain = appendString "λ " "🌍"\n', encoding="utf-8")
            result = run("eval", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: "\\955 \\127757"', result.stdout)
            result = run("eval", "--fuel", "0", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn("Normal:", result.stdout)
            for expression in ('appendString True "bad"',
                               r'(\(1 x : String) => appendString x x) "twice"',
                               r'(\(0 x : String) => appendString x "suffix") "erased"'):
                path.write_text('main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
                                '  putStrLn (' + expression + ')\n', encoding="utf-8")
                result = run("run", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_rename_preview(self):
        # ^ marks exactly the sites that may be edited; @ marks the query.
        accepted = [
            ('\\(1 ^x : Bool) => @^x', "flag"),
            ('let (^x : String) = "x 🌍" in (\\(first : String) => \\(1 second : String) => second) ^x @^x', "message"),
            ('let (1 y : String) = "outer" in let (1 ^x : String) = y in @^x', "y"),
            ('let (1 ^veryLongName : String) = "🌍" in @^veryLongName', "x"),
            ('^helper : Bool\n^helper = True\nmain : Bool\nmain = @^helper\n', "renamed"),
            ('main : IO Unit\nmain = do\n  (1 ^text : String) <- pure String "x"\n  putStrLn @^text\n', "message"),
            ('main : IO Unit\nmain = do\n  let (^text : String) = "x"\n  putStrLn ^text\n  putStrLn @^text\n', "value"),
            ('f : (0 A : Type 0) -> IO A\nf = \\(0 ^A : Type 0) => do (@^A)\n  let (A : Bool) = True\n  pure Unit ()\n', "Result"),
            ('-- λ 🌍\r\nlet (1 ^text : String) = "🌍" in @^text -- text\r\n', "renamed"),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "rename.fib"
            for marked, replacement in accepted:
                with self.subTest(source=marked, replacement=replacement):
                    chars, sites, cursor = [], [], None
                    for char in marked:
                        if char == "^":
                            sites.append(len(chars))
                        elif char == "@":
                            cursor = len(chars)
                        else:
                            chars.append(char)
                    source = "".join(chars)
                    raw = source.encode("utf-8")
                    path.write_bytes(raw)
                    line = source[:cursor].count("\n") + 1
                    column = cursor - source.rfind("\n", 0, cursor)
                    result = run("rename-preview", str(line), str(column), replacement, str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    edits = json.loads(result.stdout)["edits"]
                    self.assertEqual([edit["range"]["start"]["offset"] for edit in edits], sites)
                    changed = source
                    for edit in reversed(edits):
                        span = edit["range"]
                        changed = changed[:span["start"]["offset"]] + edit["newText"] + changed[span["end"]["offset"]:]
                    self.assertEqual(path.read_bytes(), raw, "preview must not write source")
                    path.write_bytes(changed.encode("utf-8"))
                    result = run("symbols", str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            rejected = [
                ('let (x : Bool) = True in let (y : Bool) = False in x', 1, 6, "y"),
                ('let (y : Bool) = True in let (x : Bool) = False in y', 1, 31, "y"),
                ('let (x : String) = "x" in putStrLn x', 1, 6, "putStrLn"),
                ('let (x : Bool) = True in unknown x', 1, 6, "unknown"),
                ('helper : Bool\nhelper = True\nother : Bool\nother = helper', 1, 1, "other"),
                ('main : Bool\nmain = True', 1, 1, "entry"),
                ('helper : Bool\nhelper = True', 1, 1, "main"),
                ('missing', 1, 1, "value"),
            ]
            for source, line, column, replacement in rejected:
                with self.subTest(source=source, replacement=replacement):
                    path.write_text(source, encoding="utf-8")
                    before = path.read_bytes()
                    result = run("rename-preview", str(line), str(column), replacement, str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertEqual(path.read_bytes(), before)
                    if source.startswith("let") or replacement == "other":
                        self.assertIn("lexical resolution", result.stderr)
            source = "\\(1 x : Bool) => x"
            path.write_text(source, encoding="utf-8")
            for replacement in ("", "_", "Bool", "let", "bad name", "λ", "x" * 257):
                result = run("rename-preview", "1", "5", replacement, str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            result = run("rename-preview", "1", "5", "x", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout)["edits"], [])
            # Enforce UTF-8 bytes, not scalar counts, on the proposed result.
            prefix = 'let (1 x : String) = "🌍" in x --'
            for size, succeeds in ((65534, True), (65535, False)):
                source = prefix + "a" * (size - len(prefix.encode("utf-8")))
                path.write_bytes(source.encode("utf-8"))
                result = run("rename-preview", "1", "8", "xx", str(path))
                self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)
                self.assertEqual(path.stat().st_size, size)

    def test_same_file_lexical_references(self):
        # ^ marks every expected site; @ marks the query point.
        fixtures = [
            '^first : Bool\n^first = True\nmain : Bool\nmain = @^first\n',
            'let (1 ^text : String) = "outer" in let (1 text : String) = @^text in text',
            'let (1 text : String) = "outer" in let (1 ^text : String) = text in @^text',
            'main : IO Unit\nmain = do\n  let (text : String) = "old"\n  (1 ^text : String) <- pure String text\n  putStrLn @^text\n',
            'main : IO Unit\nmain = do\n  let (1 ^text : String) = "old"\n  (1 text : String) <- pure String @^text\n  putStrLn text\n',
            'f : (0 A : Type 0) -> IO A\nf = \\(0 ^A : Type 0) => do (@^A)\n  (1 A : Bool) <- pure Bool True\n  if A then pure Unit () else pure Unit ()\n',
            '-- 🌍\r\n^item : String\r\n^item = "item"\r\nmain : String\r\nmain = (@^item) -- item\r\n',
            'let (1 ^text : String) = "text 🌍" in @^text -- text',
            '@putStrLn "prelude"',
            'main : Bool\nmain = @later\nlater : Bool\nlater = True\n',
            '\\(1 _ : String) => @_',
            'let (1 text : String) = "x" in "literal @text"',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "references.fib"
            for marked in fixtures:
                with self.subTest(source=marked):
                    chars, sites, cursor = [], [], None
                    for char in marked:
                        if char == "^":
                            sites.append(len(chars))
                        elif char == "@":
                            cursor = len(chars)
                        else:
                            chars.append(char)
                    source = "".join(chars)
                    path.write_bytes(source.encode("utf-8"))
                    line = source[:cursor].count("\n") + 1
                    column = cursor - source.rfind("\n", 0, cursor)
                    result = run("references", str(line), str(column), str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stderr, "")
                    payload = json.loads(result.stdout)
                    self.assertEqual(payload["version"], 1)
                    actual = [span["start"]["offset"] for span in payload["references"]]
                    self.assertEqual(actual, sites)
                    self.assertEqual(actual, sorted(set(actual)))
                    for span in payload["references"]:
                        token = source[span["start"]["offset"]:span["end"]["offset"]]
                        self.assertTrue(token.isidentifier())
            path.write_text("first : Bool\nfirst = True\nlater : Bool", encoding="utf-8")
            result = run("references", "1", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Parsing", result.stderr)
            result = run("references", "0", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_same_file_lexical_definition(self):
        # Mark cursor with @ and expected target with ^; neither reaches the parser.
        fixtures = [
            '@first : Bool\n^first = True\n',
            'first : Bool\n^first = True\nmain : Bool\nmain = @first\n',
            '(\\(1 ^value : String) => @value) "x"',
            'let (1 text : String) = "outer" in let (1 ^text : String) = "inner" in @text',
            'let (1 ^text : String) = "outer" in let (1 text : String) = @text in text',
            'main : IO Unit\nmain = do\n  (1 ^message : String) <- pure String "x"\n  putStrLn @message\n',
            'main : IO Unit\nmain = do\n  let (1 ^message : String) = "outer"\n  (1 message : String) <- pure String @message\n  putStrLn message\n',
            'f : (0 A : Type 0) -> IO A\nf = \\(0 ^A : Type 0) => do (@A)\n  let (A : Bool) = True\n  pure Unit ()\n',
            'f : (0 A : Type 0) -> IO A\nf = \\(0 A : Type 0) => do (A)\n  (1 ^A : Bool) <- pure Bool True\n  if @A then pure Unit () else pure Unit ()\n',
            '-- λ 🌍\r\n0 item : String\r\n^item = "🌍"\r\nmain : String\r\nmain = (@item)\r\n',
            'let (0 ignored : String) = "🌍" in let (1 ^text : String) = "x" in @text',
            '(0 ^A : Type 0) -> (1 value : @A) -> A',
            '\\(0 ^A : Type 0) => \\(1 A : @A) => A',
            'first : Bool\n^first = True\nmain : Bool\nmain =\n\t@first\n',
            # Unknown, forward, recursive, wildcard, comment/string, punctuation misses.
            '@putStrLn "external"',
            'main : Bool\nmain = @later\nlater : Bool\nlater = True\n',
            'recursive : Bool\nrecursive = @recursive\n',
            '\\(1 _ : String) => @_',
            'let (1 text : String) = "x" in "literal @text"',
            'let (1 text : String) = "x" in text -- @text',
            'let (1 text : String) = "x" in @(text)',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "navigation.fib"
            for marked in fixtures:
                with self.subTest(source=marked):
                    chars, cursor, target = [], None, None
                    for char in marked:
                        if char == "@":
                            cursor = len(chars)
                        elif char == "^":
                            target = len(chars)
                        else:
                            chars.append(char)
                    source = "".join(chars)
                    path.write_bytes(source.encode("utf-8"))
                    line = source[:cursor].count("\n") + 1
                    column = cursor - source.rfind("\n", 0, cursor)
                    result = run("definition", str(line), str(column), str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stderr, "")
                    payload = json.loads(result.stdout)
                    self.assertEqual(payload["version"], 1)
                    if target is None:
                        self.assertIsNone(payload["definition"])
                    else:
                        self.assertEqual(payload["definition"]["start"]["offset"], target)
            for text in ("0", "-1", "65538", "abc", "999999999999"):
                result = run("definition", text, "1", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("Coordinates", result.stderr)
            path.write_text("first : Bool\nfirst = True\nlater : Bool", encoding="utf-8")
            result = run("definition", "2", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Parsing", result.stderr)
            path.unlink()
            result = run("definition", "1", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_document_symbols(self):
        result = run("symbols", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["version"], 1)
        self.assertEqual([s["name"] for s in payload["symbols"]], ["finished", "main"])
        self.assertEqual(result.stderr, "")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "symbols.fib"
            source = '-- λ 🌍\r\n0 item : String\r\nitem = "🌍"\r\n\r\nhelper : Missing\r\nhelper = unknown\r\n'
            path.write_bytes(source.encode("utf-8"))
            result = run("symbols", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            symbols = json.loads(result.stdout)["symbols"]
            self.assertEqual([s["name"] for s in symbols], ["item", "helper"])
            self.assertEqual(symbols[0]["quantity"], "0")
            self.assertEqual(symbols[0]["selection"]["start"]["column"], 3)
            for symbol in symbols:
                for field in ("selection", "definitionSelection"):
                    span = symbol[field]
                    self.assertEqual(source[span["start"]["offset"]:span["end"]["offset"]],
                                     symbol["name"])
                self.assertLessEqual(symbol["range"]["start"]["offset"],
                                     symbol["selection"]["start"]["offset"])
                self.assertGreaterEqual(symbol["range"]["end"]["offset"],
                                        symbol["definitionSelection"]["end"]["offset"])
            for source in ("", "-- comment\n", "True"):
                path.write_text(source, encoding="utf-8")
                result = run("symbols", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(json.loads(result.stdout)["symbols"], [])
            for source in ("first : Bool\nfirst = True\nlater : Bool",
                           "name : Bool\nwrong = True", "\u202e"):
                path.write_text(source, encoding="utf-8")
                result = run("symbols", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(str(path), result.stderr)
            path.unlink()
            result = run("symbols", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(path), result.stderr)

    def test_annotated_do_results(self):
        result = run("run", "examples/core/do-result.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "Preparing a String result.\n"
                         "Typed do blocks can return values.\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/do-result.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        result = run("eval", "examples/core/do-result.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal:", result.stdout)
        self.assertNotIn("\nPreparing a String result.\n", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.fib"
            path.write_text(
                'main : IO Unit\nmain = do (Unit)\n'
                '  putStrLn "must not print"\n'
                '  (1 text : String) <- pure String "wrong result"\n'
                '  pure String text\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            path.write_text('main : IO String\nmain = do (String)\n'
                            '  pure String "returned"\n', encoding="utf-8")
            result = run("eval", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: (Pure "returned")', result.stdout)
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_do_let_statements(self):
        result = run("run", "examples/core/do-let.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "Pure computations belong in do blocks too.\n" +
                         "An unrestricted binding can be reused.\n" * 2)
        result = run("check", "examples/core/do-let.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "let.fib"
            prefix = 'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
            for tail in (
                '  let (1 text : String) = "unused"\n  pure Unit ()\n',
                '  let (1 text : String) = "twice"\n  putStrLn text\n  putStrLn text\n',
                '  let (0 text : String) = "erased"\n  putStrLn text\n',
                '  let (text : String) = True\n  putStrLn text\n',
                '  let (text : String) = "last"\n',
            ):
                with self.subTest(tail=tail):
                    path.write_text(prefix + tail, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
            path.write_text(prefix + '  let (1 text : String) = missing\n'
                            '  putStrLn text\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.stdout, "")
            self.assertIn(f"{path}:4:27: Resolution:", result.stderr)

    def test_typed_do_bindings(self):
        result = run("run", "examples/core/do-bindings.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "A named Fibril IO result.\n"
                         "The previous action completed.\n"
                         "Typed do bindings work.\n")
        result = run("check", "examples/core/do-bindings.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        result = run("eval", "examples/core/do-bindings.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal:", result.stdout)
        self.assertNotIn("\nTyped do bindings work.\n", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "binding.fib"
            prefix = 'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
            for tail in (
                '  (1 text : String) <- pure Bool True\n  putStrLn text\n',
                '  (1 text : String) <- pure String "unused"\n  pure Unit ()\n',
                '  (1 text : String) <- pure String "twice"\n'
                '  putStrLn text\n  putStrLn text\n',
                '  (1 text : String) <- pure String text\n  putStrLn text\n',
                '  (1 text : String) <- pure String "last"\n',
            ):
                with self.subTest(tail=tail):
                    path.write_text(prefix + tail, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.write_text(prefix + '  (1 text : String) <- pure String missing\n'
                            '  putStrLn text\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.stdout, "")
            self.assertIn(f"{path}:4:36: Resolution:", result.stderr)

    def test_io_map_is_a_checked_library_function(self):
        result = run("check", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        self.assertNotIn("Mapped result received.", result.stdout)
        result = run("run", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "The first action runs before its result is mapped.\n"
                         "Mapped result received.\n")
        self.assertEqual(result.stderr, "")
        result = run("eval", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal:", result.stdout)
        self.assertNotIn("\nMapped result received.\n", result.stdout)

    def test_expanded_io_plan_limit_has_no_output_prefix(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expanded.fib"
            path.write_text(
                'twice : IO Unit\ntwice = do\n'
                '  putStrLn "never"\n  putStrLn "never"\n'
                'main : IO Unit\nmain = do\n' + '  twice\n' * 33,
                encoding="utf-8")
            result = run("check", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("output action count limit", result.stderr)

    def test_console_do_sequence(self):
        result = run("run", "examples/core/console-sequence.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, world!\nFibril can sequence console output.\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/console-sequence.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, world!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sequence.fib"
            prefix = 'main : IO Unit\nmain = do\n  putStrLn "first"\n'
            invalid = [
                prefix + '  unknown "must not print"\n',
                prefix + '   putStrLn "bad indent"\n',
                prefix + 'putStrLn "dedented"\n',
                prefix + '  putStrLn "bad\\q"\n',
                prefix + '  putStrLn "ok" ()\n',
                'main : IO Unit\nmain = do\n',
                'main : IO Unit\nmain = do\n' + '  putStrLn "quota"\n' * 65,
            ]
            for source in invalid:
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.write_text('main : IO Unit\nmain = do\n' + '  putStrLn "quota"\n' * 64,
                            encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "quota\n" * 64)

    def test_hello_world_runner(self):
        result = run("run", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, world!\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertNotIn("Hello, world!", result.stdout)
        result = run("eval", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Hello, world!")', result.stdout)
        self.assertNotIn("\nHello, world!\n", result.stdout)
        result = run("check", "--erased", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, world!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "hello.fib"
            path.write_text('main : IO Unit\nmain =\n  putStrLn "λ 🌍\\nquote: \\" slash: \\\\ tab:\\t"\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'λ 🌍\nquote: " slash: \\ tab:\t\n')
            bad_sources = [
                'main : IO Unit\nmain = putStrLn "must not print"\nmain = putStrLn "extra"',
                'main : IO Unit\nmain = putStrLn "must not print" ()',
                'main : IO Unit\nmain = putStrLn "unterminated',
                'main : IO Unit\nmain = putStrLn "bad\\q"',
                'main : IO Unit\nmain = unknown "must not print"',
                'main : IO Bool\nmain = putStrLn "must not print"',
                'main : Bool\nmain = True',
                'main : IO Unit\nmain = putStrLn "raw\nnewline"',
            ]
            for source in bad_sources:
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.unlink()
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(path), result.stderr)

    def test_declaration_files(self):
        result = run("eval", "--fuel", "4", "examples/core/declarations.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: Bool", result.stdout)
        self.assertIn("Normal: True", result.stdout)
        result = run("check", "examples/core/declarations.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "program.fib"
            path.write_text("main : Bool\nmain = other\n", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:2:8: Resolution:", result.stdout)
            path.write_text("main : Bool\nwrong = True\n", encoding="utf-8")
            result = run("eval", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:2:1: Parsing:", result.stdout)
            self.assertIn("Expected definition of", result.stdout)

    def test_type_mismatch_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "types.fib"
            cases = [
                ("(True : Unit)", "inferred: Bool; expected: Unit"),
                ("if True then True else ()", "then: Bool; else: Unit"),
                ("() ()", "found: Unit"),
                (r"\(1 x : ()) => x", "Expected a universe; found: Unit"),
            ]
            for source, expected in cases:
                path.write_text(source, encoding="utf-8")
                for command in ("check", "eval"):
                    with self.subTest(source=source, command=command):
                        result = run(command, str(path))
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn(expected, result.stdout)
                        self.assertIn(f"{path}: Runtime checking:", result.stdout)
                        self.assertNotIn("^", result.stdout)
            path.write_text("(Type 0 : Type 0)", encoding="utf-8")
            result = run("check", "--erased", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("inferred: Type1; expected: Type0", result.stdout)

    def test_located_source_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.fib"
            path.write_bytes(b"-- comment\r\n\tmissing")
            for command in ("check", "eval"):
                with self.subTest(command=command):
                    result = run(command, str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(f"{path}:2:2: Resolution:", result.stdout)
                    self.assertIn("  2 |  missing", result.stdout)
                    self.assertIn("    |  ^", result.stdout)
            path.write_text("if True then ()", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:1:16: Parsing:", result.stdout)
            self.assertIn("Expected else", result.stdout)
            self.assertIn("^", result.stdout)
            path.write_text("@", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:1:1: Lexing:", result.stdout)
            self.assertIn("  1 | @", result.stdout)
            path.write_text("Bool", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}: Runtime checking:", result.stdout)
            self.assertNotIn("^", result.stdout)

    def test_boolean_program(self):
        result = run("eval", "examples/core/boolean.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: Bool", result.stdout)
        self.assertIn("Normal: True", result.stdout)
        result = run("eval", "--fuel", "2", "examples/core/branch-permissions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("(If v1 () v0)", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "branches.fib"
            path.write_text(r"\(1 x : Unit) => if True then x else ()", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Binder usage", result.stdout)

    def test_unit_elimination(self):
        result = run("eval", "--fuel", "2", "examples/core/consume-unit.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal: ()", result.stdout)
        result = run("eval", "--fuel", "1", "examples/core/consume-unit.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("budget exhausted", result.stdout)
        self.assertNotIn("Normal:", result.stdout)

    def test_unit_value_program(self):
        result = run("eval", "examples/core/unit.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: Unit", result.stdout)
        self.assertIn("Normal: ()", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "discard.fib"
            path.write_text(r"\(1 x : Unit) => ()", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Binder usage", result.stdout)

    def test_typed_local_binding(self):
        result = run("check", "examples/core/local-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = run("eval", "examples/core/local-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal: (Lam 1 Type0 v0)", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "recursive.fib"
            path.write_text("let (1 x : Type 0) = x in x", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unbound name", result.stdout)

    def test_source_ascription(self):
        result = run("check", "examples/core/identity-annotated.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("(Pi 0 Type0 (Pi 1 v0 v1))", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ascription.fib"
            path.write_text("(Type 0 : Type 0)", encoding="utf-8")
            result = run("check", "--erased", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("not compatible", result.stdout)

    def test_checked_reference_evaluation(self):
        path = "examples/core/evaluate-identity.fib"
        result = run("eval", path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("not compiled execution", result.stdout)
        self.assertIn("Normal: (Lam 1 Type0 v0)", result.stdout)
        result = run("eval", "--fuel", "0", path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("budget exhausted", result.stdout)
        self.assertNotIn("Normal:", result.stdout)
        result = run("eval", "--fuel", "0", "examples/core/identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout)
        for value in ("-1", "4097", "99999999999", "wrong"):
            with self.subTest(fuel=value):
                result = run("eval", "--fuel", value, path)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Fuel must", result.stdout)
        result = run("eval", "examples/core/identity-type.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Runtime", result.stdout)

    def test_unsupported_commands_fail(self):
        for args in (("build", "example.fib"), ("demo", "extra"), ("--unknown",)):
            with self.subTest(args=args):
                result = run(*args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Unsupported command", result.stdout)


if __name__ == "__main__":
    unittest.main()
