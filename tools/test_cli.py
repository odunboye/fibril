#!/usr/bin/env python3
"""Smoke-test the built CLI independently of its pure implementation helpers."""
from pathlib import Path
import subprocess
import shutil
import signal
import time
from unittest.mock import patch
import tempfile
import random
import unittest
import json
import os
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "build/exec/fibril"


def run_cli(*args, cwd=ROOT, text=True, timeout=20):
    command = [str(EXE), *args]
    # The executable is a shell wrapper: its Chez child inherits both pipes.
    # Killing only the wrapper can leave communicate() waiting indefinitely.
    process = subprocess.Popen(command, cwd=cwd, text=text, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(command, timeout, output=stdout, stderr=stderr)
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def run(*args, cwd=ROOT):
    return run_cli(*args, cwd=cwd)


class CLITests(unittest.TestCase):
    def test_mutual_nat_forwarding_alias_plans(self):
        bases = ['flag', 'if flag then False else False', 'if flag then False else True',
                 'if flag then True else False', 'if flag then True else True']
        for base_index, base in enumerate(bases):
            for bits in range(16):
                order0, order1, alias_first, target_first = [bool(bits & (1 << bit)) for bit in range(4)]
                orders = {'first': order0, 'second': order1}
                alias, worker = ('first', 'second') if alias_first else ('second', 'first')
                target = 'first' if target_first else 'second'
                call = lambda name, n, p: f'{name} {n} {p}' if orders[name] else f'{name} {p} {n}'
                declarations = []
                for name in ['first', 'second']:
                    signature = '(1 n : Nat) -> (1 p : Bool)' if orders[name] else '(1 p : Bool) -> (1 n : Nat)'
                    binders = 'count flag' if orders[name] else 'flag count'
                    if name == alias:
                        body = call(worker, 'count', 'flag')
                    else:
                        body = f'case count of\n    Succ previous => {call(target, "previous", "flag")}\n    Zero => {base}'
                    declarations.append(f'  {name} : {signature} -> Bool\n  {name} {binders} = {body}')
                observations, expected = [], []
                for name in ['first', 'second']:
                    for flag in [False, True]:
                        value = flag if base_index == 0 else [False, not flag, flag, True][base_index - 1]
                        for n in ['Zero', '(Succ Zero)', '(Succ (Succ Zero))']:
                            expression = call(name, n, 'True' if flag else 'False')
                            observations.append(f'  putStrLn (if {expression} then "T" else "F")')
                            expected.append('T' if value else 'F')
                with self.subTest(base=base_index, bits=bits), tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / 'Main.fib'
                    path.write_text('module Main\nmutual where\n' + '\n'.join(declarations) +
                                    '\nmain : IO Unit\nmain = do\n' + '\n'.join(observations) + '\n')
                    result = run('run', '--source-dir', directory, str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stdout, '\n'.join(expected) + '\n')

    def test_mutual_nat_forwarding_alias_boundaries_and_navigation(self):
        fixture = (ROOT / 'examples/modules/mutual-parity/Reordered.fib').read_text()
        mutations = [
            ('first count flag = second flag count', 'first count flag = first count flag'),
            ('second flag count = case count of\n    Zero => if flag then False else True\n    Succ previous => first previous flag', 'second flag count = first count flag'),
            ('second flag count = case count of', 'second flag count = case flag of'),
            ('second flag count', 'second count flag'),
            ('first count flag = second flag count', 'first count flag = second count flag'),
            ('second flag count', 'second True count'),
            ('second flag count', 'second flag (Succ count)'),
            ('first previous flag', 'first count flag'),
            ('first previous flag', 'first previous True'),
            ('first previous flag', 'first flag previous'),
            ('first previous flag', 'Reordered.first previous flag'),
            ('first count flag = second flag count', 'first count flag = if True then second flag count else second flag count'),
            ('first count flag = second flag count', 'first count flag = second flag'),
            ('first count flag = second flag count', 'first count flag = second flag count flag'),
            ('(1 flag : Bool)', '(flag : Bool)'),
            ('(1 flag : Bool)', '(0 flag : Bool)'),
            ('(1 count : Nat)', '(1 count : Bool)'),
            ('first count flag =', 'first count first ='),
            ('Succ previous =>', 'Succ flag =>'),
            ('Zero => if flag then False else True', 'Zero => True'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Reordered.fib'
            for old, new in mutations:
                with self.subTest(new=new):
                    path.write_text(fixture.replace(old, new))
                    result = run('check', '--source-dir', directory, str(path))
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            path.write_text(fixture.replace('second flag count\n', '((second) flag) count\n'))
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            lines = formatted.stdout.splitlines()
            alias_line = next(i for i, text in enumerate(lines, 1) if 'first count flag =' in text)
            worker_line = next(i for i, text in enumerate(lines, 1) if 'second flag count =' in text)
            succ_line = next(i for i, text in enumerate(lines, 1) if '=> first previous flag' in text)
            for line, token, expected_line in [(alias_line, 'second', worker_line), (succ_line, 'first', alias_line),
                                               (succ_line, 'previous', succ_line), (succ_line, 'flag', worker_line),
                                               (alias_line, 'flag', alias_line), (alias_line, 'count', alias_line)]:
                column = lines[line - 1].rindex(token) + 1
                ref = run('definition', '--source-dir', directory, '--entry', str(path), str(line), str(column), str(path))
                self.assertEqual(ref.returncode, 0, ref.stdout + ref.stderr)
                report = json.loads(ref.stdout)
                self.assertTrue(report['checked'])
                self.assertEqual(report['definition']['range']['start']['line'], expected_line)
            main = Path(directory) / 'Main.fib'
            main.write_text('module Main\nimport Reordered (first)\nmain : IO Unit\nmain = putStrLn (if first (Succ Zero) False then "yes" else "no")\n')
            args = ['--source-dir', directory, str(main)]
            result = run('run', *args)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'yes\n')
            valid = path.read_text()
            path.write_text(valid.replace('Zero => if flag then False else True', 'Zero => True'))
            self.assertNotEqual(run('check', *args).returncode, 0)
            path.write_text(valid.replace('export\n', ''))
            self.assertNotEqual(run('check', *args).returncode, 0)

    def test_mutual_nat_payload_tables(self):
        for bits in range(64):
            values = [bool(bits & (1 << bit)) for bit in range(6)]
            bases, targets = [values[:2], values[2:4]], values[4:]
            boolean = lambda bit: 'True' if bit else 'False'
            target = lambda bit: 'first' if bit else 'second'
            observations, expected = [], []
            for entry, name in enumerate(['first', 'second']):
                for flag in [False, True]:
                    for count in range(3):
                        nat = 'Zero'
                        for _ in range(count):
                            nat = f'(Succ {nat})'
                        observations.append(f'  putStrLn (if {name} {nat} {boolean(flag)} then "T" else "F")')
                        state = entry
                        for _ in range(count):
                            state = 0 if targets[state] else 1
                        expected.append('T' if bases[state][0 if flag else 1] else 'F')
            with self.subTest(bits=bits), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'Main.fib'
                path.write_text(f'''module Main
mutual where
  first : (1 n : Nat) -> (1 flag : Bool) -> Bool
  first n flag = case n of
    Zero => if flag then {boolean(bases[0][0])} else {boolean(bases[0][1])}
    Succ previous => {target(targets[0])} previous flag
  second : (1 m : Nat) -> (1 payload : Bool) -> Bool
  second m payload = case m of
    Succ previous => {target(targets[1])} previous payload
    Zero => if payload then {boolean(bases[1][0])} else {boolean(bases[1][1])}
main : IO Unit
main = do
''' + '\n'.join(observations) + '\n')
                result = run('run', '--source-dir', directory, str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, '\n'.join(expected) + '\n')

    def test_mutual_nat_payload_ownership_and_call_boundary(self):
        fixture = (ROOT / 'examples/modules/mutual-parity/Payload.fib').read_text()
        mutations = [
            ('second previous flag', 'second previous True'),
            ('second previous flag', 'second previous (if flag then False else True)'),
            ('second previous flag', 'second flag previous'),
            ('second previous flag', 'second previous'),
            ('second previous flag', 'second previous flag flag'),
            ('second previous flag', 'second count flag'),
            ('second previous flag', 'second (Succ previous) flag'),
            ('Zero => flag', 'Zero => True'),
            ('Zero => flag', 'Zero => if True then flag else flag'),
            ('Zero => flag', 'Zero => if flag then flag else flag'),
            ('(1 flag : Bool)', '(flag : Bool)'),
            ('(1 flag : Bool)', '(0 flag : Bool)'),
            ('first count flag =', 'first count ='),
            ('first count flag =', 'first count second ='),
            ('Succ previous => second previous flag', 'Succ flag => second flag flag'),
            ('second : (1 count : Nat) -> (1 flag : Bool) -> Bool', 'second : (1 count : Nat) -> Bool'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Payload.fib'
            for old, new in mutations:
                with self.subTest(new=new):
                    path.write_text(fixture.replace(old, new))
                    result = run('check', '--source-dir', directory, str(path))
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            path.write_text(fixture.replace('second previous flag', '((second) previous) flag'))
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            lines = formatted.stdout.splitlines()
            line = next(i for i, text in enumerate(lines, 1) if '=> ((second) previous) flag' in text)
            col = lines[line - 1].index('second') + 1
            result = run('definition', '--source-dir', directory, '--entry', str(path), str(line), str(col), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target_line = next(i for i, text in enumerate(lines, 1) if text.startswith('  second count flag ='))
            self.assertEqual(json.loads(result.stdout)['definition']['range']['start']['line'], target_line)
            # Call-site spans must not capture the predecessor/payload references.
            for token, expected_line in [('previous', line), ('flag', next(i for i, text in enumerate(lines, 1) if text.startswith('  first count flag =')))]:
                column = lines[line - 1].rindex(token) + 1
                ref = run('definition', '--source-dir', directory, '--entry', str(path), str(line), str(column), str(path))
                self.assertEqual(ref.returncode, 0, ref.stdout + ref.stderr)
                self.assertEqual(json.loads(ref.stdout)['definition']['range']['start']['line'], expected_line)
            main = Path(directory) / 'Main.fib'
            main.write_text('module Main\nimport Payload (first)\nmain : IO Unit\nmain = putStrLn (if first (Succ Zero) False then "yes" else "no")\n')
            imported = run('run', '--source-dir', directory, str(main))
            self.assertEqual(imported.returncode, 0, imported.stdout + imported.stderr)
            self.assertEqual(imported.stdout, 'yes\n')
            source = path.read_text()
            path.write_text(source.replace('Zero => if flag then False else True', 'Zero => True'))
            self.assertNotEqual(run('check', '--source-dir', directory, str(main)).returncode, 0)

    def test_mutual_nat_selector_tables(self):
        # Every base/transition table, not just the even/odd cross-call case.
        for bits in range(16):
            b0, b1, t0, t1 = [bool(bits & (1 << bit)) for bit in range(4)]
            target = lambda bit: 'first' if bit else 'second'
            boolean = lambda bit: 'True' if bit else 'False'
            with self.subTest(bits=bits), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                path = root / 'Main.fib'
                observations, expected = [], []
                for entry, name in enumerate(['first', 'second']):
                    for count in range(4):
                        nat = 'Zero'
                        for _ in range(count):
                            nat = f'(Succ {nat})'
                        observations.append(f'  putStrLn (if {name} {nat} then "T" else "F")')
                        state = entry
                        for _ in range(count):
                            state = 0 if [t0, t1][state] else 1
                        expected.append('T' if [b0, b1][state] else 'F')
                path.write_text(f'''module Main
mutual where
  first : (1 n : Nat) -> Bool
  first n = case n of
    Zero => {boolean(b0)}
    Succ previous => {target(t0)} previous
  second : (1 n : Nat) -> Bool
  second n = case n of
    Succ previous => {target(t1)} previous
    Zero => {boolean(b1)}
main : IO Unit
main = do
''' + '\n'.join(observations) + '\n')
                result = run('run', '--source-dir', directory, str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, '\n'.join(expected) + '\n')

    def test_mutual_nat_fail_closed_source_boundary(self):
        source = '''module Main
mutual where
  first : (1 n : Nat) -> Bool
  first n = case n of
    Zero => True
    Succ previous => second previous
  second : (1 n : Nat) -> Bool
  second n = case n of
    Zero => False
    Succ previous => first previous
main : Bool
main = first Zero
'''
        mutations = [
            ('second previous', 'second n'),
            ('second previous', 'second (Succ previous)'),
            ('second previous', 'first'),
            ('second previous', 'second previous previous'),
            ('second previous', 'Main.second previous'),
            ('second previous', 'if True then second previous else first previous'),
            ('Zero => False', 'Zero => missing'),
            ('Zero => False', 'Succ other => False'),
            ('(1 n : Nat)', '(0 n : Nat)'),
            ('(1 n : Nat)', '(n : Nat)'),
            ('second : (1 n : Nat) -> Bool', 'second : (1 n : Bool) -> Bool'),
            ('  second n = case n of', '  second n = case Zero of'),
            ('    Succ previous => first previous', '    Succ first => first first'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            for old, new in mutations:
                with self.subTest(new=new):
                    path.write_text(source.replace(old, new))
                    result = run('check', '--json', '--source-dir', directory, str(path))
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            # Neither source order nor group placement enables ordinary forward refs.
            path.write_text(source.replace('mutual where', 'earlier : Bool\nearlier = first Zero\nmutual where'))
            self.assertNotEqual(run('check', '--source-dir', directory, str(path)).returncode, 0)
            # A headerless adapter must not silently flatten/drop the group.
            path.write_text(source.replace('module Main\n', ''))
            self.assertNotEqual(run('check', str(path)).returncode, 0)

    def test_mutual_nat_group_framing_and_shadowing(self):
        fixture = (ROOT / 'examples/modules/mutual-parity/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            invalid = [
                fixture.replace('  even :', '  export\n  even :'),
                fixture[:fixture.index('  odd :')],
                fixture.replace('main : IO Unit', '  third : Bool\n  third = True\nmain : IO Unit'),
                fixture.replace('  odd :', '  mutual where\n  odd :'),
                fixture.replace('  odd :', '  even :'),
                fixture.replace('mutual where', 'Zero : Nat\nZero = Succ Zero\nmutual where'),
                fixture.replace('mutual where', 'Nat : Type\nNat = Bool\nmutual where'),
                fixture.replace('mutual where', 'mutual'),
            ]
            for number, source in enumerate(invalid):
                with self.subTest(number=number):
                    path.write_text(source)
                    result = run('check', '--source-dir', directory, str(path))
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_mutual_nat_import_format_and_navigation(self):
        fixture = (ROOT / 'examples/modules/mutual-parity/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            parity = root / 'Parity.fib'
            parity.write_text(fixture.split('main : IO Unit')[0].replace('module Main', 'module Parity'))
            main = root / 'Main.fib'
            main.write_text('module Main\nimport Parity (odd)\nmain : IO Unit\nmain = putStrLn (if odd (Succ Zero) then "yes" else "no")\n')
            args = ['--source-dir', directory, str(main)]
            result = run('run', *args)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'yes\n')
            formatted = run('format', str(parity))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            parity.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(parity)).returncode, 0)
            self.assertEqual(run('check', *args).returncode, 0)
            lines = parity.read_text().splitlines()
            call_line = next(i for i, line in enumerate(lines, 1) if '=> odd predecessor' in line)
            column = lines[call_line - 1].index('odd') + 1
            definition = run('definition', '--source-dir', directory, '--entry', str(main),
                             str(call_line), str(column), str(parity))
            self.assertEqual(definition.returncode, 0, definition.stdout + definition.stderr)
            report = json.loads(definition.stdout)
            self.assertTrue(report['checked'])
            target_line = next(i for i, line in enumerate(lines, 1) if line.startswith('  odd n ='))
            self.assertEqual(report['definition']['range']['start']['line'], target_line)
            self.assertEqual(report['definition']['range']['start']['column'], 3)
            symbols = json.loads(run('symbols', str(parity)).stdout)['symbols']
            self.assertEqual([symbol['name'] for symbol in symbols], ['even', 'odd'])
            self.assertTrue(all(symbol['exported'] for symbol in symbols))
            self.assertNotEqual(run('elaborate', str(parity)).returncode, 0)
            # An invalid unselected member prevents the whole interface publishing.
            valid = parity.read_text()
            parity.write_text(valid.replace('Zero => True', 'Zero => missing'))
            self.assertNotEqual(run('check', *args).returncode, 0)
            parity.write_bytes(valid.replace('\n', '\r\n').encode())
            formatted_crlf = run_cli('format', str(parity), text=False)
            self.assertEqual(formatted_crlf.returncode, 0, formatted_crlf.stderr)
            self.assertIn(b'\r\n', formatted_crlf.stdout)
            parity.write_text(valid)
            parity.write_text(parity.read_text().replace('export\n', ''))
            self.assertNotEqual(run('check', *args).returncode, 0)

    def test_pure_bytes_check_and_eval(self):
        path = 'examples/core/bytes-pure.fib'
        checked = run('check', path)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        evaluated = run('eval', path)
        self.assertEqual(evaluated.returncode, 0, evaluated.stdout + evaluated.stderr)
        self.assertIn('Normal: (Succ (Succ Zero))', evaluated.stdout)

    def test_bytes_cannot_cross_text_write_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'bytes.fib'
            path.write_text('main : IO Unit\nmain = putStrLn (primBytesOctetMod256 Zero)\n')
            for command in ('check', 'run', 'run-interactive', 'emit-c', 'emit-c-interactive'):
                result = run(command, str(path))
                self.assertNotEqual(result.returncode, 0, (command, result.stdout, result.stderr))

    def test_timeout_cleans_up_wrapper_children_with_open_pipes(self):
        with tempfile.TemporaryDirectory() as directory:
            wrapper = Path(directory) / 'wrapper'
            wrapper.write_text('#!/bin/sh\nsleep 30 &\nwait\n')
            wrapper.chmod(0o700)
            start = time.monotonic()
            with patch(__name__ + '.EXE', wrapper):
                with self.assertRaises(subprocess.TimeoutExpired):
                    run_cli(timeout=0.2)
            self.assertLess(time.monotonic() - start, 5)

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
            path.write_text("Type 1234567", encoding="utf-8")
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
            result = run("run", str(path), cwd=directory)
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
                    result = run_cli("format", str(path), text=False)
                    self.assertEqual(result.returncode, 0, result.stderr.decode())
                    self.assertEqual(result.stdout, formatted.encode())
                    self.assertEqual(path.read_bytes(), data.encode())
                    path.write_bytes(result.stdout)
                    again = run_cli("format", str(path), text=False)
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
                text = run_cli("format", str(file), text=False)
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
                raw = run_cli("format", str(path), text=False)
                self.assertEqual(raw.stdout, expected.replace("\n", ending).encode())
                self.assertEqual(path.read_bytes(), original)
                report = json.loads(run("format", "--json", str(path)).stdout)
                self.assertEqual(report["original"].encode(), original)
                self.assertEqual(report["formatted"].encode(), raw.stdout)
                self.assertEqual(run("format", "--check", str(path)).returncode, 1)
                path.write_bytes(raw.stdout)
                canonical = path.read_bytes()
                again = run_cli("format", str(path), text=False)
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

    def test_email_request_api_direct_cases_and_separate_tests(self):
        import shutil
        fixture = ROOT / 'examples/packages/request-api'
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory) / 'request-api'
            shutil.copytree(fixture, project)
            manifest = project / 'fibril.yaml'
            checked = run('check', '--package', str(manifest))
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            result = run('test', '--package', str(manifest))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            suite = project / 'test/src/RequestTests/Main.fib'
            baseline = suite.read_text()
            cases = [
                ('Mail.Request.describe (Mail.Request.Enqueue "ada@example.test")', 'enqueue for ada@example.test'),
                ('Mail.Request.describe (Mail.Request.Preview "receipt")', 'preview receipt'),
                ('Mail.Request.describe Mail.Request.Health', 'health request'),
                ('inspect (Mail.Request.Enqueue "ada@example.test")', 'enqueue:ada@example.test'),
                ('inspect (Mail.Request.Preview "receipt")', 'preview:receipt'),
                ('inspect Mail.Request.Health', 'health'),
            ]
            before_main = baseline[:baseline.index('main = ')]
            for expression, expected in cases:
                with self.subTest(expression=expression):
                    suite.write_text(before_main + f'main = equalString ({expression}) "{expected}"\n')
                    tested = run('test', '--package', str(manifest))
                    self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
            suite.write_text(before_main + 'main = equalString (inspect Mail.Request.Health) "wrong"\n')
            failed = run('test', '--package', str(manifest))
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn('Tests: failed', failed.stderr)
            suite.write_text(baseline)
            source = project / 'src/Mail/Request.fib'
            source.write_text(source.read_text().replace('  Health => "health request"\n', ''))
            self.assertNotEqual(run('check', '--package', str(manifest)).returncode, 0)
            self.assertNotEqual(run('test', '--package', str(manifest)).returncode, 0)

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

    def test_direct_unary_recursive_data_cases(self):
        source = ('module Main\ndata Chain : Type where\n  eliminator foldChain\n'
                  '  Empty : Chain\n  More : (1 rest : Chain) -> Chain\n'
                  'drop : (1 value : Chain) -> Chain\ndrop value = case value of\n'
                  '  Empty => Empty\n  More rest => rest\n'
                  'marks : (1 value : Chain) -> String\nmarks value = foldChain (\\(0 self : Chain) => String) "" '
                  '(\\(0 rest : Chain) => \\(1 result : String) => appendString result "!") value\n'
                  'main : IO Unit\nmain = putStrLn (marks (drop (More (More Empty))))\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '!\n')
            explicit = source.replace('case value of', 'case value return (\\(0 self : Chain) => Chain) of')
            path.write_text(explicit)
            self.assertEqual(project('run').stdout, '!\n')
            reversed_arms = source.replace('  Empty => Empty\n  More rest => rest', '  More rest => rest\n  Empty => Empty')
            path.write_text(reversed_arms)
            self.assertEqual(project('run').stdout, '!\n')
            aliases = ('emptyAlias : Chain\nemptyAlias = Empty\n'
                       'moreAlias : (1 item : Chain) -> Chain\nmoreAlias item = More item\n')
            path.write_text(source.replace('drop :', aliases + 'drop :').replace('  Empty => Empty\n  More rest => rest',
                                                                                  '  emptyAlias => Empty\n  moreAlias rest => rest'))
            self.assertEqual(project('run').stdout, '!\n')
            # A dependent expected result is abstracted over the actual
            # scrutinee, and the successor branch consumes the real tail.
            dependent = ('module Main\ndata Chain : Type where\n  eliminator foldChain\n'
                         '  Empty : Chain\n  More : (1 rest : Chain) -> Chain\n'
                         'data Tagged (0 chain : Chain) : Type where\n  Bad : Tagged chain\n'
                         '  Mark : (1 text : String) -> Tagged chain\n'
                         'build : (1 value : Chain) -> Tagged value\nbuild value = case value of\n'
                         '  Empty => Mark Empty "empty"\n'
                         '  More rest => Mark (More rest) (foldChain (\\(0 self : Chain) => String) "tail" '
                         '(\\(0 r : Chain) => \\(1 text : String) => appendString text "!") rest)\n'
                         'show : (0 value : Chain) -> (1 tagged : Tagged value) -> String\n'
                         'show value tagged = case tagged of\n  Bad => "bad"\n  Mark text => text\n'
                         'main : IO Unit\nmain = putStrLn (show (More Empty) (build (More Empty)))\n')
            path.write_text(dependent)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'tail\n')
            path.write_text(dependent.replace('case value of', 'case value return (\\(0 self : Chain) => Tagged self) of'))
            self.assertEqual(project('run').stdout, 'tail\n')
            # Imported aliases must be checked values of this exact family.
            other = ('data Other : Type where\n  Stop : Other\n  Again : (1 rest : Other) -> Other\n')
            duplicate = ('combine : (1 left : Chain) -> (1 right : Chain) -> Chain\n'
                         'combine left right = foldChain (\\(0 self : Chain) => Chain) left '
                         '(\\(0 tail : Chain) => \\(1 result : Chain) => More result) right\n')
            invalid = [source.replace('  More rest => rest', '  More rest => Empty'),
                       source.replace('drop :', duplicate + 'drop :').replace('  More rest => rest', '  More rest => combine rest rest'),
                       source.replace('  More rest => rest', '  More => Empty'),
                       source.replace('  More rest => rest', '  Empty => Empty'),
                       source.replace('  More rest => rest\n', ''),
                       source.replace('drop :', other + 'drop :').replace('  More rest => rest', '  Again rest => rest')]
            for program in invalid:
                with self.subTest(program=program[-180:]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            # A linear capture may be shared across alternatives but not
            # discarded in one of them.
            shared = ('module Main\ndata Chain : Type where\n  eliminator foldChain\n  Empty : Chain\n'
                      '  More : (1 rest : Chain) -> Chain\n'
                      'use : (1 prefix : String) -> (1 value : Chain) -> String\n'
                      'use prefix value = case value of\n  Empty => prefix\n'
                      '  More rest => foldChain (\\(0 self : Chain) => String) prefix '
                      '(\\(0 r : Chain) => \\(1 x : String) => appendString x "!") rest\n'
                      'main : IO Unit\nmain = putStrLn (use "ok" (More Empty))\n')
            path.write_text(shared)
            self.assertEqual(project('run').stdout, 'ok\n')
            path.write_text(shared.replace('  Empty => prefix', '  Empty => "dropped"'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            shadow = source.replace('drop : (1 value : Chain)', 'drop : (More : String) -> (1 value : Chain)')
            shadow = shadow.replace('drop value = case value', 'drop More value = case value').replace('drop (More (More Empty))', 'drop "shadow" (More (More Empty))')
            path.write_text(shadow)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('shadowed', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # A large transparent constructor alias is rejected by guarded
            # conversion; naming the original constructor remains available.
            # Shared bodies fit the syntax cap; spend an extra local beta step
            # per call to test conversion exhaustion below the parser depth cap.
            expression = 'More value'
            for _ in range(50):
                expression = 'identity (' + expression + ')'
            budgeted = ('module Main\ndata Chain : Type where\n  Empty : Chain\n  More : (1 rest : Chain) -> Chain\n'
                        'identity : (1 x : Chain) -> Chain\nidentity x = let (1 copy : Chain) = x in copy\n'
                        'alias : (1 value : Chain) -> Chain\nalias value = ' + expression + '\n'
                        'inspect : (1 value : Chain) -> Chain\ninspect value = case value of\n'
                        '  Empty => Empty\n  alias rest => rest\nmain : IO Unit\nmain = putStrLn "ok"\n')
            path.write_text(budgeted)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('constructor comparison exhausted', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            path.write_text(budgeted.replace('  alias rest => rest', '  More rest => rest'))
            self.assertEqual(project('run').stdout, 'ok\n')

    def test_structural_calls_in_exclusive_conditionals(self):
        import re
        source = (ROOT / 'examples/modules/conditional-recursion/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'TT\nFF\nTT\nFF\na!b!\na?b?\n')
            lines = source.splitlines()
            for name, definition in [('natMarks', 'natMarks flag count ='),
                                     ('chainMarks', 'chainMarks flag chain ='),
                                     ('join', 'join flag items =')]:
                sites = [(row, line.index('(' + name + ' ') + 2)
                         for row, line in enumerate(lines, 1) if '(' + name + ' flag ' in line]
                # Exclude calls in main: only the authored step's alternatives.
                sites = [(row, col) for row, col in sites if row < next(i for i, line in enumerate(lines, 1) if line.startswith('main :'))]
                self.assertEqual(len(sites), 2)
                expected = next(i for i, line in enumerate(lines, 1) if line.startswith(definition))
                for row, col in sites:
                    nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
                    self.assertEqual(nav.returncode, 0, nav.stderr)
                    start = json.loads(nav.stdout)['definition']['range']['start']
                    self.assertEqual((start['line'], start['column']), (expected, 1))
            # The original single-argument Nat lowering has the same rule.
            legacy = ('module Main\nchoose : (1 n : Nat) -> String\nchoose n = case n of\n'
                      '  Zero => ""\n  Succ previous => if True then appendString "a" (choose previous) '
                      'else appendString "b" (choose previous)\n'
                      'main : IO Unit\nmain = putStrLn (choose (Succ (Succ Zero)))\n')
            path.write_text(legacy)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'aa\n')
            nested = legacy.replace('if True then appendString "a" (choose previous) else appendString "b" (choose previous)',
                                    'if True then (if True then appendString "a" (choose previous) else appendString "b" (choose previous)) else appendString "c" (choose previous)')
            path.write_text(nested)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'aa\n')
            nestedLines = nested.splitlines()
            row = next(i for i, line in enumerate(nestedLines, 1) if line.startswith('  Succ previous =>'))
            line = nestedLines[row - 1]
            offsets = [match.start() for match in re.finditer(r'choose previous', line)]
            self.assertEqual(len(offsets), 3)
            targetRow = next(i for i, line in enumerate(nestedLines, 1) if line.startswith('choose n ='))
            for offset in offsets:
                nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(offset + 1), str(path))
                self.assertEqual(nav.returncode, 0, nav.stderr)
                start = json.loads(nav.stdout)['definition']['range']['start']
                self.assertEqual((start['line'], start['column']), (targetRow, 1))
            # An erased declaration is checked at the erased stage; runtime
            # branch-use claims do not apply to this non-runtime definition.
            erased = legacy.replace('choose :', '0 choose :').replace(
                'else appendString "b" (choose previous)', 'else "erased"').replace(
                'main = putStrLn (choose (Succ (Succ Zero)))', 'main = putStrLn "checked"')
            path.write_text(erased)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'checked\n')
            # The one-erased-parameter implicit omission path also accepts both
            # alternatives, preserving the linear head on either path.
            poly = (ROOT / 'examples/modules/polymorphic-recursion/Main.fib').read_text().replace(
                '  Prepend head tail => Prepend head (copy tail)',
                '  Prepend head tail => if True then Prepend head (copy tail) else Prepend head (copy tail)')
            poly = poly[:poly.index('main : IO Unit')] + 'main : IO Unit\nmain = putStrLn "checked"\n'
            path.write_text(poly)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'checked\n')
            polyLines = poly.splitlines()
            row = next(i for i, line in enumerate(polyLines, 1) if 'then Prepend head (copy tail) else Prepend head (copy tail)' in line)
            line = polyLines[row - 1]
            first = line.index('copy tail')
            second = line.index('copy tail', first + 1)
            targetRow = next(i for i, line in enumerate(polyLines, 1) if line.startswith('copy Element items ='))
            for offset in [first, second]:
                nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(offset + 1), str(path))
                self.assertEqual(nav.returncode, 0, nav.stderr)
                start = json.loads(nav.stdout)['definition']['range']['start']
                self.assertEqual((start['line'], start['column']), (targetRow, 1))
            grouped = source.replace('(chainMarks flag tail)', '((chainMarks) flag tail)', 1)
            path.write_text(grouped)
            groupedLines = grouped.splitlines()
            row = next(i for i, line in enumerate(groupedLines, 1) if '((chainMarks) flag tail)' in line)
            offset = groupedLines[row - 1].index('chainMarks)')
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(offset + 1), str(path))
            self.assertIsNotNone(json.loads(nav.stdout)['definition'])
            punctuation = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(offset), str(path))
            self.assertIsNone(json.loads(punctuation.stdout)['definition'])
            # Calls on the same execution path, mismatched tails and an absent
            # branch use remain rejected. No output occurs on checking failure.
            invalid = [source.replace('then appendString "T" (natMarks flag previous)',
                                      'then appendString (natMarks flag previous) (natMarks flag previous)', 1),
                       source.replace('else appendString "F" (natMarks flag previous)', 'else "missing"', 1),
                       source.replace('else appendString "F" (chainMarks flag tail)',
                                      'else appendString "F" (chainMarks flag (More tail))', 1),
                       source.replace('if flag\n    then appendString "T" (natMarks flag previous)',
                                      'if equalString (natMarks flag previous) ""\n    then appendString "T" (natMarks flag previous)', 1),
                       source.replace('else appendString head (appendString "?" (join flag tail))',
                                      'else appendString "dropped" (join flag tail)')]
            for program in invalid:
                with self.subTest(program=program[200:700]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'TT\nFF\nTT\nFF\na!b!\na?b?\n')

    def test_uniform_structural_nat_and_unary_telescope(self):
        import shutil
        fixture = ROOT / 'examples/modules/uniform-nat-chain'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture, root, dirs_exist_ok=True)
            path = root / 'Main.fib'
            source = path.read_text()
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'receipt!!\n~~\n')
            # Both constructors can be supplied in either source order.
            reversed_arms = source.replace('  Zero => initial\n  Succ previous => transform (iterate {Element} transform initial previous)',
                                          '  Succ previous => transform (iterate {Element} transform initial previous)\n  Zero => initial')
            reversed_arms = reversed_arms.replace('  Data.Chain.Empty => ""\n  Data.Chain.More previous => appendString marker (marks marker previous)',
                                                '  Data.Chain.More previous => appendString marker (marks marker previous)\n  Data.Chain.Empty => ""')
            path.write_text(reversed_arms)
            self.assertEqual(project('run').stdout, 'receipt!!\n~~\n')
            # Test empty branches and the actual authored recursive sites.
            empty = source.replace('(Succ (Succ Zero))', 'Zero').replace('(Data.Chain.More (Data.Chain.More Data.Chain.Empty))', 'Data.Chain.Empty')
            path.write_text(empty)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'receipt\n\n')
            path.write_text(source)
            lines = source.splitlines()
            for use, definition in [('iterate {Element} transform initial previous', 'iterate Element transform initial count ='),
                                    ('marks marker previous', 'marks marker chain =')]:
                row = next(i for i, line in enumerate(lines, 1) if use in line)
                col = lines[row - 1].index(use) + 1
                nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
                self.assertEqual(nav.returncode, 0, nav.stderr)
                target = json.loads(nav.stdout)['definition']['range']['start']
                self.assertEqual((target['line'], target['column']), (next(i for i, line in enumerate(lines, 1) if line.startswith(definition)), 1))
            iterate_call = 'iterate {Element} transform initial previous'
            marks_call = 'marks marker previous'
            invalid = [source.replace(iterate_call, 'iterate {String} transform initial previous'),
                       source.replace(iterate_call, 'iterate {Element} transform initial count'),
                       source.replace(iterate_call, 'iterate {Element} transform initial (Succ previous)'),
                       source.replace(iterate_call, 'iterate {Element} transform initial initial'),
                       source.replace(iterate_call, 'iterate transform initial previous'),
                       source.replace(iterate_call, 'Main.iterate {Element} transform initial previous'),
                       source.replace(iterate_call, 'iterate {Element} transform (transform initial) previous'),
                       source.replace('  Zero => initial', '  Zero => iterate {Element} transform initial Zero'),
                       source.replace('(transform : (1 value : A) -> A)', '(1 transform : (1 value : A) -> A)'),
                       source.replace(marks_call, 'marks marker chain'),
                       source.replace(marks_call, 'marks marker (Data.Chain.More previous)'),
                       source.replace('  Data.Chain.More previous =>', '  Data.Chain.More marker =>'),
                       source.replace('import Data.Chain\n', 'import Data.Chain\nZero : Bool\nZero = True\n')]
            for program in invalid:
                with self.subTest(program=program[80:420]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            # Changing the prefix argument is not a uniform-prefix shape, but the chain
            # argument still shrinks, so general recursion accepts it.
            path.write_text(source.replace(marks_call, 'marks "changed" previous'))
            changed_prefix = project('run')
            self.assertEqual(changed_prefix.returncode, 0, changed_prefix.stdout + changed_prefix.stderr)
            self.assertEqual(changed_prefix.stdout, 'receipt!!\n~changed\n')
            # A different recursive family must not stand in for a constructor.
            other = ('data Other : Type where\n  End : Other\n  Next : (1 tail : Other) -> Other\n')
            path.write_text(source.replace('marks :', other + 'marks :').replace('  Data.Chain.More previous =>', '  Next previous =>'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            dependent = ('module Main\nimport Data.Chain\n'
                         'data Tagged (0 c : Data.Chain.Chain) : Type where\n  Tag : Tagged c\n'
                         'broken : (prefix : String) -> (1 c : Data.Chain.Chain) -> Tagged c\n'
                         'broken prefix c = case c of\n  Data.Chain.Empty => Tag Data.Chain.Empty\n'
                         '  Data.Chain.More tail => broken prefix tail\n'
                         'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(dependent)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('result independent', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # Admission at the uniform-prefix boundary for both unary shapes.
            for family in ['Nat', 'Chain']:
                for count in [64, 65]:
                    names = [f'p{i}' for i in range(count)]
                    signature = ' -> '.join(f'({name} : String)' for name in names) + f' -> (1 xs : {family}) -> String'
                    header = ' '.join(names + ['xs'])
                    call = ' '.join(['visit'] + names + ['tail'])
                    data = '' if family == 'Nat' else 'data Chain : Type where\n  Empty : Chain\n  More : (1 tail : Chain) -> Chain\n'
                    terminal, successor = ('Zero', 'Succ') if family == 'Nat' else ('Empty', 'More')
                    program = ('module Main\n' + data + f'visit : {signature}\nvisit {header} = case xs of\n'
                               f'  {terminal} => ""\n  {successor} tail => appendString p0 ({call})\n'
                               'main : IO Unit\nmain = putStrLn "admitted"\n')
                    path.write_text(program)
                    result = project('run')
                    if count == 64:
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertEqual(result.stdout, 'admitted\n')
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(result.stdout, '')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'receipt!!\n~~\n')

    def test_uniform_structural_sequence_telescope(self):
        source = (ROOT / 'examples/modules/uniform-recursion/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'yes,no,\n')
            lines = source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if '(renderItems {Element} render separator tail)' in line)
            col = lines[row - 1].index('renderItems {Element}') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            target = json.loads(nav.stdout)['definition']['range']['start']
            self.assertEqual((target['line'], target['column']), (next(i for i, line in enumerate(lines, 1) if line.startswith('renderItems Element render separator items =')), 1))
            explicit = source.replace('renderItems : {0 A : Type}', 'renderItems : (0 A : Type)').replace('renderItems {Element} render separator tail', 'renderItems Element render separator tail').replace('renderItems {Bool} showBool', 'renderItems Bool showBool')
            path.write_text(explicit)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'yes,no,\n')
            # The result may depend on erased telescope parameters, just not on
            # the structural input; reusable arguments stay fixed on recursion.
            mapper = (ROOT / 'examples/modules/polymorphic-map/Main.fib').read_text()
            mapper = mapper.replace('(1 items : Items A) -> Items B', '(unused : String) -> (1 items : Items A) -> Items B')
            mapper = mapper.replace('mapItems A B transform items =', 'mapItems A B transform unused items =')
            mapper = mapper.replace('mapItems {A} {B} transform tail', 'mapItems {A} {B} transform unused tail')
            mapper = mapper.replace('mapItems {String} {String} exclaim\n', 'mapItems {String} {String} exclaim "unused"\n')
            path.write_text(mapper)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'hello! world!\n')
            # An erased non-Type parameter and a concrete list element are
            # allowed when the recursive call repeats that parameter exactly.
            flag = ('module Main\ndata Items {0 A : Type} : Type where\n  Empty : Items A\n'
                    '  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                    'render : (0 flag : Bool) -> (1 xs : Items String) -> String\n'
                    'render flag xs = case xs of\n  Empty => ""\n'
                    '  Prepend head tail => appendString head (render flag tail)\n'
                    'main : IO Unit\nmain = putStrLn (render True (Prepend "ok" (Empty {String})))\n')
            path.write_text(flag)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'ok\n')
            call = 'renderItems {Element} render separator tail'
            invalid = [source.replace(call, 'renderItems {Bool} render separator tail'),
                       source.replace(call, 'renderItems {Element} showBool separator tail'),
                       source.replace(call, 'renderItems {Element} render ":" tail'),
                       source.replace(call, 'renderItems {Element} separator render tail'),
                       source.replace(call, 'renderItems {Element} render separator items'),
                       source.replace(call, 'renderItems {Element} render separator (Prepend head tail)'),
                       source.replace(call, 'renderItems render separator tail'),
                       source.replace(call, 'Main.renderItems {Element} render separator tail'),
                       source.replace('(render : (1 item : A) -> String)', '(1 render : (1 item : A) -> String)'),
                       source.replace('appendString (render head)', 'appendString "discarded"'),
                       source.replace('  Prepend head tail =>', '  Prepend tail tail =>')]
            for program in invalid:
                with self.subTest(program=program[120:480]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            for count in [64, 65]:
                names = [f'p{i}' for i in range(count)]
                signature = ' -> '.join(f'({name} : String)' for name in names) + ' -> (1 xs : Items String) -> String'
                header = ' '.join(names + ['xs'])
                call = ' '.join(['visit'] + names + ['tail'])
                admitted = ('module Main\ndata Items {0 A : Type} : Type where\n  Empty : Items A\n'
                            '  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n' +
                            f'visit : {signature}\nvisit {header} = case xs of\n  Empty => ""\n'
                            f'  Prepend head tail => appendString head ({call})\n'
                            'main : IO Unit\nmain = putStrLn "admitted"\n')
                path.write_text(admitted)
                result = project('run')
                if count == 64:
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stdout, 'admitted\n')
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, '')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'yes,no,\n')

    def test_polymorphic_structural_mapping_equations(self):
        source = (ROOT / 'examples/modules/polymorphic-map/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'hello! world!\n')
            # Constructor identity comes from a checked direct import as well.
            import re
            (Path(directory) / 'Data').mkdir()
            (Path(directory) / 'Data/Items.fib').write_text((ROOT / 'examples/modules/recursive-list/Data/Items.fib').read_text())
            declaration = source[source.index('data Items'):source.index('mapItems :')]
            imported = source.replace(declaration, '')
            for short, qualified in [('Items', 'Data.Items.Items'), ('foldItems', 'Data.Items.foldItems'),
                                     ('Empty', 'Data.Items.Empty'), ('Prepend', 'Data.Items.Prepend')]:
                imported = re.sub(r'\b' + short + r'\b', qualified, imported)
            imported = imported.replace('module Main\n', 'module Main\nimport Data.Items\n')
            path.write_text(imported)
            imported_result = project('run')
            self.assertEqual(imported_result.returncode, 0, imported_result.stdout + imported_result.stderr)
            self.assertEqual(imported_result.stdout, 'hello! world!\n')
            path.write_text(source)
            # Recursive self-call navigation is recorded from successful lowering.
            lines = source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if '(mapItems {A} {B} transform tail)' in line)
            col = lines[row - 1].index('mapItems {A}') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            target = json.loads(nav.stdout)['definition']['range']['start']
            self.assertEqual((target['line'], target['column']), (next(i for i, line in enumerate(lines, 1) if line.startswith('mapItems A B transform items =')), 1))
            reversed_arms = source.replace('  Empty => Empty {B}\n  Prepend head tail => Prepend (transform head) (mapItems {A} {B} transform tail)',
                                           '  Prepend head tail => Prepend (transform head) (mapItems {A} {B} transform tail)\n  Empty => Empty {B}')
            path.write_text(reversed_arms)
            self.assertEqual(project('run').stdout, 'hello! world!\n')
            different = source.replace('exclaim : (1 text : String) -> String\nexclaim text = appendString text "!"',
                                       'exclaim : (1 flag : Bool) -> String\nexclaim flag = if flag then "T" else "F"')
            different = different.replace('mapItems {String} {String} exclaim', 'mapItems {Bool} {String} exclaim').replace('Prepend "hello" (Prepend " world" (Empty {String}))', 'Prepend True (Prepend False (Empty {Bool}))')
            path.write_text(different)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'TF\n')
            path.write_text(source.replace('Prepend "hello" (Prepend " world" (Empty {String}))', 'Empty {String}'))
            self.assertEqual(project('run').stdout, '\n')
            call = 'mapItems {A} {B} transform tail'
            bad_calls = ['mapItems {B} {B} transform tail', 'mapItems {A} {A} transform tail',
                         'mapItems {A} {B} exclaim tail', 'mapItems {A} {B} transform items',
                         'mapItems {A} {B} transform (Prepend head tail)',
                         'mapItems {A} transform tail', 'mapItems transform tail',
                         'Main.mapItems {A} {B} transform tail']
            invalid = [source.replace(call, replacement) for replacement in bad_calls]
            invalid += [source.replace('(transform : (1 value : A) -> B)', '(1 transform : (1 value : A) -> B)'),
                        source.replace('Prepend (transform head) (mapItems {A} {B} transform tail)',
                                       'Prepend (transform head) (mapItems {A} {B} transform (mapItems {A} {A} (\\(1 x : A) => x) tail))'),
                        source.replace('Prepend head tail =>', 'Prepend tail tail =>'),
                        source.replace('  Empty => Empty {B}', '  Empty => mapItems {A} {B} transform (Empty {A})')]
            for program in invalid:
                with self.subTest(program=program[180:580]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            # The same signature and case without a recursive self-call must
            # fall back to ordinary direct-case elaboration, not be rewritten.
            replacement = ('  Prepend head tail => foldItems A (\\(0 ys : Items A) => Items B) '
                           '(Prepend (transform head) (Empty {B})) '
                           '(\\(1 item : A) => \\(0 rest : Items A) => \\(1 result : Items B) => Prepend (transform item) result) tail')
            nonrecursive = source.replace('  Prepend head tail => Prepend (transform head) (mapItems {A} {B} transform tail)', replacement)
            nonrecursive = nonrecursive[:nonrecursive.index('main : IO Unit')] + 'main : IO Unit\nmain = putStrLn "checked"\n'
            path.write_text(nonrecursive)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'checked\n')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'hello! world!\n')

    def test_checked_structural_self_call_navigation(self):
        import shutil
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / 'examples/modules/recursive-data', root, dirs_exist_ok=True)
            path = root / 'Main.fib'
            source = path.read_text().replace('(marksByEquation rest)', '((marksByEquation) rest)')
            path.write_text(source)
            lines = source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if '((marksByEquation) rest)' in line)
            start = lines[row - 1].index('marksByEquation')
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(start + 1), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            target = json.loads(nav.stdout)['definition']['range']['start']
            definition_row = next(i for i, line in enumerate(lines, 1) if line.startswith('marksByEquation chain ='))
            self.assertEqual((target['line'], target['column']), (definition_row, 1))
            # Parentheses around the authored name are not part of its span.
            punctuation = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(start), str(path))
            self.assertIsNone(json.loads(punctuation.stdout)['definition'])
            poly = (ROOT / 'examples/modules/polymorphic-recursion/Main.fib').read_text().replace('copy tail', 'copy {Element} tail')
            path.write_text(poly)
            lines = poly.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if '(copy {Element} tail)' in line)
            col = lines[row - 1].index('copy {Element} tail') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
            target = json.loads(nav.stdout)['definition']['range']['start']
            self.assertEqual((target['line'], target['column']), (next(i for i, line in enumerate(lines, 1) if line.startswith('copy Element items =')), 1))
            # An earlier imported homonym remains an ordinary call, not a
            # recursive self-reference merely because the body looks similar.
            (root / 'Data').mkdir(exist_ok=True)
            (root / 'Data/Helper.fib').write_text('module Data.Helper\nimport Data.Chain\nexport\nmarks : (1 c : Data.Chain.Chain) -> String\nmarks c = Data.Chain.foldChain (\\(0 x : Data.Chain.Chain) => String) "first" (\\(0 x : Data.Chain.Chain) => \\(1 r : String) => r) c\n')
            ordinary = ('module Main\nimport Data.Chain\nimport Data.Helper\n'
                        'marks : (1 c : Data.Chain.Chain) -> String\nmarks c = case c of\n'
                        '  Data.Chain.Empty => "empty"\n  Data.Chain.More tail => marks tail\n'
                        'main : IO Unit\nmain = putStrLn (marks (Data.Chain.More Data.Chain.Empty))\n')
            path.write_text(ordinary)
            lines = ordinary.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if '=> marks tail' in line)
            col = lines[row - 1].index('marks tail') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            definition = json.loads(nav.stdout)['definition']
            self.assertEqual(Path(definition['path']).name, 'Helper.fib')
            # Checked sites from a dependency module must reach project navigation.
            helper = root / 'Data/Helper.fib'
            helper_source = ('module Data.Helper\nimport Data.Chain\nexport\n'
                             'marks : (1 c : Data.Chain.Chain) -> String\nmarks c = case c of\n'
                             '  Data.Chain.Empty => ""\n'
                             '  Data.Chain.More tail => appendString "!" (marks tail)\n')
            helper.write_text(helper_source)
            path.write_text('module Main\nimport Data.Chain\nimport Data.Helper\nmain : IO Unit\nmain = putStrLn (Data.Helper.marks Data.Chain.Empty)\n')
            lines = helper_source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if '(marks tail)' in line)
            col = lines[row - 1].index('marks tail') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(helper))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            definition = json.loads(nav.stdout)['definition']
            self.assertEqual(Path(definition['path']).name, 'Helper.fib')
            self.assertEqual(definition['range']['start']['line'], 5)

    def test_polymorphic_structural_sequence_equations(self):
        source = (ROOT / 'examples/modules/polymorphic-recursion/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'hello world\n')
            path.write_text(source.replace('copy tail', 'copy {Element} tail'))
            self.assertEqual(project('run').stdout, 'hello world\n')
            explicit = source.replace('copy : {0 A : Type}', 'copy : (0 A : Type)').replace('copy tail', 'copy Element tail').replace('join (copy (Prepend', 'join (copy String (Prepend')
            path.write_text(explicit)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'hello world\n')
            reversed_arms = source.replace('  Empty => Empty {Element}\n  Prepend head tail => Prepend head (copy tail)',
                                           '  Prepend head tail => Prepend head (copy tail)\n  Empty => Empty {Element}')
            path.write_text(reversed_arms)
            self.assertEqual(project('run').stdout, 'hello world\n')
            # Different result type depending on the erased parameter, but not
            # on the structural input, is retained by the checked fold.
            invalid = [source.replace('copy tail', 'copy items'),
                       source.replace('copy tail', 'copy (Prepend head tail)'),
                       source.replace('copy tail', 'copy {String} tail'),
                       source.replace('Prepend head (copy tail)', 'Prepend head (copy {Bool} tail)'),
                       source.replace('Prepend head (copy tail)', 'copy tail'),
                       source.replace('Prepend head (copy tail)', 'Prepend head (Prepend head (copy tail))'),
                       source.replace('  Empty => Empty {Element}', '  Empty => copy (Empty {Element})'),
                       explicit.replace('copy Element tail', 'copy String tail'),
                       explicit.replace('copy Element tail', 'copy tail'),
                       source.replace('  Prepend head tail =>', '  Prepend tail tail =>')]
            for program in invalid:
                with self.subTest(program=program[150:450]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'hello world\n')

    def test_linear_accumulator_as_checked_function_valued_fold(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        args = ['--source-dir', str(fixture), str(fixture / 'Main.fib')]
        result = run('run', *args)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'bac\n')
        source = (fixture / 'Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Main.fib'
            path.write_text(source)
            lines = source.splitlines()
            call_line = next(i for i, line in enumerate(lines, 1) if '=> reverseOnto tail' in line)
            call_column = lines[call_line - 1].index('reverseOnto tail') + 1
            definition_line = next(i for i, line in enumerate(lines, 1) if line.startswith('reverseOnto items acc ='))
            navigation = run('definition', '--source-dir', str(root), '--entry', str(path),
                             str(call_line), str(call_column), str(path))
            self.assertEqual(navigation.returncode, 0, navigation.stderr)
            self.assertEqual(json.loads(navigation.stdout)['definition']['range']['start']['line'], definition_line)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(run('run', '--source-dir', str(root), str(path)).stdout, 'bac\n')
            arms = ('  Data.Items.Empty => acc\n'
                    '  Data.Items.Prepend head tail => reverseOnto tail (Data.Items.Prepend head acc)')
            self.assertIn(arms, source)
            path.write_text(source.replace(arms, '\n'.join(reversed(arms.splitlines()))))
            self.assertEqual(run('run', '--source-dir', str(root), str(path)).stdout, 'bac\n')
            original = 'Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))'
            for value, expected in [('Data.Items.Empty {String}', 'c\n'),
                                    ('Data.Items.Prepend "a" (Data.Items.Empty {String})', 'ac\n')]:
                path.write_text(source.replace(original, value))
                checked = run('run', '--source-dir', str(root), str(path))
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                self.assertEqual(checked.stdout, expected)
            variants = [source.replace('reverseOnto tail (Data.Items.Prepend head acc)', 'reverseOnto tail acc'),
                        source.replace('reverseOnto tail (Data.Items.Prepend head acc)',
                                       'reverseOnto tail (Data.Items.Prepend head (Data.Items.Prepend head acc))'),
                        source.replace('reverseOnto tail (Data.Items.Prepend head acc)',
                                       'reverseOnto items (Data.Items.Prepend head acc)'),
                        source.replace('Data.Items.Empty => acc', 'Data.Items.Empty => Data.Items.Empty {String}')]
            for invalid in variants:
                self.assertNotEqual(invalid, source)
                path.write_text(invalid)
                rejected = run('run', '--source-dir', str(root), str(path))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
            # Checking the constructor's value is not enough: the authored call
            # must respect explicit versus implicit erased arguments.
            short = source[:source.index('main : IO Unit')] + 'main : IO Unit\nmain = putStrLn "checked"\n'
            alias_type = ('consAlias : {binder} -> (1 h : A) -> (1 t : Data.Items.Items A) -> Data.Items.Items A\n'
                          'consAlias T h t = Data.Items.Prepend h t\n')
            for binder, succeeds in [('{0 A : Type}', True), ('(0 A : Type)', False)]:
                baseline = short.replace('reverseOnto :', alias_type.format(binder=binder) + 'reverseOnto :')
                path.write_text(baseline)
                self.assertEqual(run('check', '--source-dir', str(root), str(path)).returncode, 0)
                applied = baseline.replace('reverseOnto tail (Data.Items.Prepend head acc)',
                                           'reverseOnto tail (consAlias head acc)')
                path.write_text(applied)
                checked = run('check', '--source-dir', str(root), str(path))
                self.assertEqual(checked.returncode == 0, succeeds, checked.stdout + checked.stderr)

    def test_linear_accumulator_checked_general_updates(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = (fixture / 'Main.fib').read_text()
        example = run('run', '--source-dir', str(fixture), str(fixture / 'Decorated.fib'))
        self.assertEqual(example.returncode, 0, example.stdout + example.stderr)
        self.assertEqual(example.stdout, 'b!a!c\n')
        original = 'reverseOnto tail (Data.Items.Prepend head acc)'
        self.assertIn(original, source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Main.fib'
            def project(program):
                path.write_text(program)
                return run('run', '--source-dir', str(root), str(path))
            decorated = source.replace(original, 'reverseOnto tail (Data.Items.Prepend (appendString head "!") acc)')
            result = project(decorated)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'b!a!c\n')
            conditional = source.replace(original,
                'reverseOnto tail (if True then Data.Items.Prepend (appendString head "!") acc else Data.Items.Prepend head acc)')
            short = lambda program: program[:program.index('join :')] + 'main : IO Unit\nmain = putStrLn "checked"\n'
            result = project(short(conditional))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            global_tail = ('tail : Data.Items.Items String\ntail = Data.Items.Empty {String}\n'
                           'items : Data.Items.Items String\nitems = Data.Items.Empty {String}\n')
            with_globals = short(source).replace('reverseOnto :', global_tail + 'reverseOnto :')
            self.assertEqual(project(with_globals).returncode, 0)
            helpers = (global_tail + 'other : Data.Items.Items String\nother = Data.Items.Empty {String}\n'
                       'consume : (1 xs : Data.Items.Items String) -> String\nconsume xs = case xs of\n'
                       '  Data.Items.Empty => ""\n'
                       '  Data.Items.Prepend h t => appendString h (consume t)\n'
                       'stamp : {0 tag : Data.Items.Items String} -> (1 h : String) -> (1 xs : Data.Items.Items String) -> Data.Items.Items String\n'
                       'stamp tag h xs = Data.Items.Prepend h xs\n')
            scoped = short(source).replace('reverseOnto :', helpers + 'reverseOnto :')
            safe_global = scoped.replace(original, 'reverseOnto tail (Data.Items.Prepend (appendString head (consume other)) acc)')
            safe_implicit = scoped.replace(original, 'reverseOnto tail (stamp {other} head acc)')
            for valid in [safe_global, safe_global.replace('consume other', 'consume Main.other'),
                          safe_global.replace('consume other', 'consume Main.tail'), safe_implicit]:
                checked = project(valid)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                self.assertEqual(checked.stdout, 'checked\n')
            invalid = [safe_global.replace('consume other', 'consume tail'),
                       safe_global.replace('consume other', 'consume items'),
                       with_globals.replace(original, 'reverseOnto tail (Data.Items.Prepend head tail)'),
                       with_globals.replace(original, 'reverseOnto tail (Data.Items.Prepend head items)'),
                       short(source).replace(original, 'reverseOnto tail (Data.Items.Prepend head (reverseOnto tail acc))'),
                       short(source).replace(original, 'reverseOnto tail (Data.Items.Prepend head (reverseOnto items acc))'),
                       short(source).replace(original, 'reverseOnto tail (Data.Items.Prepend (appendString head head) acc)')]
            for program in invalid:
                rejected = project(program)
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)
            # An erased use of the tail is outside the narrow accumulator recognizer but
            # terminates, so the general recursion path accepts it.
            erased_tail = project(safe_implicit.replace('stamp {other}', 'stamp {tail}'))
            self.assertEqual(erased_tail.returncode, 0, erased_tail.stdout + erased_tail.stderr)
            self.assertEqual(erased_tail.stdout, 'checked\n')
            # Likewise a linear let inside the update expression.
            with_let = project(short(source).replace(original, 'reverseOnto tail (let (1 x : String) = head in Data.Items.Prepend x acc)'))
            self.assertEqual(with_let.returncode, 0, with_let.stdout + with_let.stderr)
            self.assertEqual(with_let.stdout, 'checked\n')

    def test_structural_list_with_distinct_linear_string_accumulator(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = (fixture / 'StringAccumulator.fib').read_text()
        initial = 'Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))'
        update = 'appendOnto tail (appendString acc head)'
        self.assertIn(initial, source)
        self.assertIn(update, source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'StringAccumulator.fib'
            def project(program):
                path.write_text(program)
                return run('run', '--source-dir', str(root), str(path))
            for value, expected in [(initial, 'cab\n'), ('Data.Items.Empty {String}', 'c\n'),
                                    ('Data.Items.Prepend "a" (Data.Items.Empty {String})', 'ca\n')]:
                result = project(source.replace(initial, value))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, expected)
            computed_base = source.replace('Data.Items.Empty => acc', 'Data.Items.Empty => appendString acc "!"')
            result = project(computed_base)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'cab!\n')
            arms = ('  Data.Items.Empty => acc\n'
                    '  Data.Items.Prepend head tail => appendOnto tail (appendString acc head)')
            self.assertIn(arms, source)
            result = project(source.replace(arms, '\n'.join(reversed(arms.splitlines()))))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'cab\n')
            alias = ('0 TextType : Type\nTextType = String\n' + source[source.index('appendOnto :'):])
            alias = source[:source.index('appendOnto :')] + alias.replace('(1 acc : String) -> String', '(1 acc : TextType) -> TextType')
            result = project(alias)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'cab\n')
            erased = source[:source.index('main : IO Unit')].replace('appendOnto :', '0 appendOnto :') + 'main : IO Unit\nmain = putStrLn "checked"\n'
            result = project(erased)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            invalid = [source.replace('(1 acc : String) -> String', '(1 acc : String) -> Bool'),
                       source.replace('(1 acc : String) -> String', '(acc : String) -> String'),
                       source.replace('(1 acc : String) -> String', '(0 acc : String) -> String'),
                       source.replace(update, 'appendOnto items (appendString acc head)'),
                       source.replace(update, 'appendOnto tail (appendString acc acc)'),
                       source.replace(update, 'appendOnto tail acc'),
                       source.replace('Data.Items.Empty => acc', 'Data.Items.Empty => "bad"')]
            for program in invalid:
                self.assertNotEqual(program, source)
                rejected = project(program)
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)

    def test_structural_accumulator_computed_base_and_distinct_result(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = (fixture / 'Matches.fib').read_text()
        items = 'Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))'
        base = 'Data.Items.Empty => equalString acc "cab"'
        self.assertIn(items, source)
        self.assertIn(base, source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Matches.fib'
            def project(program):
                path.write_text(program)
                return run('run', '--source-dir', str(root), str(path))
            for program, expected in [(source, 'matched\n'),
                                      (source.replace(items, 'Data.Items.Empty {String}').replace('"c"\n  then', '"cab"\n  then'), 'matched\n'),
                                      (source.replace(items, 'Data.Items.Prepend "a" (Data.Items.Empty {String})'), 'different\n')]:
                result = project(program)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, expected)
            conditional = source.replace(base, 'Data.Items.Empty => if True then equalString acc "cab" else equalString acc "other"')
            result = project(conditional)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'matched\n')
            # A cons-branch binder is not in scope in the empty branch; an
            # unrelated global with that spelling remains a legal reference.
            globals_ = 'head : String\nhead = "cab"\ntail : String\ntail = "cab"\n'
            with_globals = source.replace('matchesOnto :', globals_ + 'matchesOnto :')
            for name in ['head', 'tail']:
                result = project(with_globals.replace(base, 'Data.Items.Empty => equalString acc ' + name))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, 'matched\n')
            helpers = ('items : Data.Items.Items String\nitems = Data.Items.Empty {String}\n'
                       'other : Data.Items.Items String\nother = Data.Items.Empty {String}\n'
                       'consume : (1 xs : Data.Items.Items String) -> String\nconsume xs = case xs of\n'
                       '  Data.Items.Empty => ""\n'
                       '  Data.Items.Prepend h t => appendString h (consume t)\n')
            short = source[:source.index('main : IO Unit')].replace('matchesOnto :', helpers + 'matchesOnto :')
            short += 'main : IO Unit\nmain = putStrLn "checked"\n'
            safe = short.replace(base, 'Data.Items.Empty => equalString acc (consume other)')
            checked = project(safe)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertEqual(checked.stdout, 'checked\n')
            for collision in ['items']:
                rejected = project(safe.replace('consume other', 'consume ' + collision))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)
            # A qualified name denotes the global, not the pattern variable, so it is valid.
            qualified = project(safe.replace('consume other', 'consume Matches.items'))
            self.assertEqual(qualified.returncode, 0, qualified.stdout + qualified.stderr)
            self.assertEqual(qualified.stdout, 'checked\n')
            invalid = [source.replace(base, 'Data.Items.Empty => True'),
                       source.replace(base, 'Data.Items.Empty => equalString acc acc'),
                       source.replace(base, 'Data.Items.Empty => matchesOnto items acc')]
            for program in invalid:
                self.assertNotEqual(program, source)
                rejected = project(program)
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)
            # A let in the base arm is outside the narrow recognizer but still terminates.
            with_let = project(source.replace(base, 'Data.Items.Empty => let (1 x : String) = acc in equalString x "cab"'))
            self.assertEqual(with_let.returncode, 0, with_let.stdout + with_let.stderr)
            self.assertEqual(with_let.stdout, 'matched\n')

    def test_accumulator_first_structural_equations(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = (fixture / 'AccumulatorFirst.fib').read_text()
        initial = 'Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))'
        recursive = 'matchesFrom (appendString acc head) tail'
        self.assertIn(initial, source)
        self.assertIn(recursive, source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'AccumulatorFirst.fib'
            def project(program, command='run'):
                path.write_text(program)
                return run(command, '--source-dir', str(root), str(path))
            for program, expected in [(source, 'matched\n'),
                                      (source.replace(initial, 'Data.Items.Empty {String}').replace('matchesFrom "c"', 'matchesFrom "cab"'), 'matched\n'),
                                      (source.replace(initial, 'Data.Items.Prepend "a" (Data.Items.Empty {String})'), 'different\n')]:
                result = project(program)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, expected)
            arms = ('  Data.Items.Empty => equalString acc "cab"\n'
                    '  Data.Items.Prepend head tail => matchesFrom (appendString acc head) tail')
            self.assertIn(arms, source)
            result = project(source.replace(arms, '\n'.join(reversed(arms.splitlines()))))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'matched\n')
            path.write_text(source)
            lines = source.splitlines()
            call_line = next(i for i, line in enumerate(lines, 1) if '=> matchesFrom (appendString' in line)
            call_column = lines[call_line - 1].index('matchesFrom (appendString') + 1
            target_line = next(i for i, line in enumerate(lines, 1) if line.startswith('matchesFrom acc items ='))
            navigation = run('definition', '--source-dir', str(root), '--entry', str(path), str(call_line), str(call_column), str(path))
            self.assertEqual(navigation.returncode, 0, navigation.stderr)
            self.assertEqual(json.loads(navigation.stdout)['definition']['range']['start']['line'], target_line)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            formatted_run = run('run', '--source-dir', str(root), str(path))
            self.assertEqual(formatted_run.returncode, 0, formatted_run.stdout + formatted_run.stderr)
            self.assertEqual(formatted_run.stdout, 'matched\n')
            helpers = ('items : Data.Items.Items String\nitems = Data.Items.Empty {String}\n'
                       'tail : Data.Items.Items String\ntail = Data.Items.Empty {String}\n'
                       'other : Data.Items.Items String\nother = Data.Items.Empty {String}\n'
                       'consume : (1 xs : Data.Items.Items String) -> String\nconsume xs = case xs of\n'
                       '  Data.Items.Empty => ""\n'
                       '  Data.Items.Prepend h t => appendString h (consume t)\n')
            short = source[:source.index('main : IO Unit')].replace('matchesFrom :', helpers + 'matchesFrom :')
            short += 'main : IO Unit\nmain = putStrLn "checked"\n'
            safe = short.replace(recursive, 'matchesFrom (appendString acc (appendString head (consume other))) tail')
            checked = project(safe)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            for collision in ['items', 'tail']:
                rejected = project(safe.replace('consume other', 'consume ' + collision))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)
            # A qualified name denotes the global, not the pattern variable, so it is valid.
            qualified = project(safe.replace('consume other', 'consume AccumulatorFirst.tail'))
            self.assertEqual(qualified.returncode, 0, qualified.stdout + qualified.stderr)
            self.assertEqual(qualified.stdout, 'checked\n')
            invalid = [source.replace(recursive, 'matchesFrom (appendString acc head) items'),
                       source.replace(recursive, 'matchesFrom tail (appendString acc head)'),
                       source.replace(recursive, 'matchesFrom (appendString acc acc) tail'),
                       source.replace(recursive, 'matchesFrom (appendString acc head) (Data.Items.Prepend head tail)'),
                       source.replace(recursive, 'matchesFrom acc tail'),
                       source.replace('(1 acc : String)', '(acc : String)'),
                       source.replace('(1 items : Data.Items.Items String)', '(items : Data.Items.Items String)')]
            for program in invalid:
                self.assertNotEqual(program, source)
                rejected = project(program)
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)

    def test_accumulator_equations_with_uniform_prefixes(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        sources = [(fixture / 'UniformPrefix.fib', 'b!a!c\n'),
                   (fixture / 'UniformPrefixFirst.fib', 'ca!b!?\n')]
        for path, expected in sources:
            result = run('run', '--source-dir', str(fixture), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, expected)
        source = sources[0][0].read_text()
        recursive = 'reverseMappedOnto {Input} {Output} transform tail'
        self.assertIn(recursive, source)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'UniformPrefix.fib'
            def project(program, command='run'):
                path.write_text(program)
                return run(command, '--source-dir', str(root), str(path))
            lines = source.splitlines()
            call_line = next(i for i, line in enumerate(lines, 1) if recursive in line)
            call_column = lines[call_line - 1].index(recursive) + 1
            target_line = next(i for i, line in enumerate(lines, 1) if line.startswith('reverseMappedOnto Input Output transform items acc ='))
            path.write_text(source)
            navigation = run('definition', '--source-dir', str(root), '--entry', str(path), str(call_line), str(call_column), str(path))
            self.assertEqual(navigation.returncode, 0, navigation.stderr)
            self.assertEqual(json.loads(navigation.stdout)['definition']['range']['start']['line'], target_line)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            formatted_run = run('run', '--source-dir', str(root), str(path))
            self.assertEqual(formatted_run.returncode, 0, formatted_run.stdout + formatted_run.stderr)
            self.assertEqual(formatted_run.stdout, 'b!a!c\n')
            short = source[:source.index('mark :')] + 'main : IO Unit\nmain = putStrLn "checked"\n'
            baseline = project(short)
            self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
            explicit = source.replace('{0 A : Type}', '(0 A : Type)').replace('{0 B : Type}', '(0 B : Type)')
            explicit = explicit.replace('{Input} {Output} transform tail', 'Input Output transform tail')
            explicit = explicit.replace('{String} {String} mark', 'String String mark')
            observed = project(explicit)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            self.assertEqual(observed.stdout, 'b!a!c\n')
            input_list = 'Data.Items.Prepend "a" (Data.Items.Prepend "b" (Data.Items.Empty {String}))'
            self.assertIn(input_list, source)
            for value, expected in [('Data.Items.Empty {String}', 'c\n'),
                                    ('Data.Items.Prepend "a" (Data.Items.Empty {String})', 'a!c\n')]:
                observed = project(source.replace(input_list, value))
                self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
                self.assertEqual(observed.stdout, expected)
            invalid = [short.replace(recursive, 'reverseMappedOnto {Input} {Input} transform tail'),
                       short.replace(recursive, 'reverseMappedOnto {Input} {Output} tail'),
                       short.replace(recursive, 'reverseMappedOnto {Input} {Output} transform items'),
                       short.replace(recursive, 'reverseMappedOnto {Input} {Output} transform (Data.Items.Prepend head tail)'),
                       short.replace('(transform : (1 value : A) -> B)', '(1 transform : (1 value : A) -> B)'),
                       short.replace(recursive, 'reverseMappedOnto {Input} {Output} (\\(1 x : Input) => transform x) tail'),
                       short.replace('transform', 'head'),
                       short.replace('(Data.Items.Prepend (transform head) acc)',
                                     '(Data.Items.Prepend (transform head) (reverseMappedOnto {Input} {Output} transform tail acc))')]
            for program in invalid:
                self.assertNotEqual(program, short)
                rejected = project(program)
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)
            first_source = sources[1][0].read_text()
            first_short = first_source[:first_source.index('mark :')] + 'main : IO Unit\nmain = putStrLn "checked"\n'
            path = root / 'UniformPrefixFirst.fib'
            baseline = project(first_short)
            self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
            first_call = 'appendMappedFrom {Element} render suffix (appendString acc (render head)) tail'
            self.assertIn(first_call, first_short)
            for replacement in ['appendMappedFrom {Element} render "?" (appendString acc (render head)) tail',
                                'appendMappedFrom {Element} render suffix (appendString acc (render head)) items',
                                'appendMappedFrom render suffix (appendString acc (render head)) tail']:
                rejected = project(first_short.replace(first_call, replacement))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)

    def test_accumulator_uniform_prefix_rejects_type_correct_changes(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        source = ('module Main\nimport Data.Items\n'
                  'other : (1 value : String) -> String\nother value = value\n'
                  'fold : {0 Tag : Type} -> (transform : (1 value : String) -> String) -> '
                  '(1 items : Data.Items.Items String) -> (1 acc : String) -> String\n'
                  'fold Tag transform items acc = case items of\n'
                  '  Data.Items.Empty => acc\n'
                  '  Data.Items.Prepend head tail => fold {Tag} transform tail (appendString acc (transform head))\n'
                  'main : IO Unit\nmain = putStrLn "checked"\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Main.fib'
            path.write_text(source)
            baseline = run('check', '--source-dir', str(root), str(path))
            self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
            for changed in [source.replace('fold {Tag} transform tail', 'fold {String} transform tail'),
                            source.replace('fold {Tag} transform tail', 'fold {Tag} other tail')]:
                self.assertNotEqual(changed, source)
                path.write_text(changed)
                rejected = run('check', '--source-dir', str(root), str(path))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertNotIn('Expanded core construction budget exhausted', rejected.stderr)

    def test_accumulator_uniform_prefix_admission_boundary(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Main.fib'
            def program(count):
                names = ' '.join(f'p{i}' for i in range(count))
                prefix = ' -> '.join(f'(0 p{i} : Type)' for i in range(count))
                return ('module Main\nimport Data.Items\n'
                        f'fold : {prefix} -> (1 items : Data.Items.Items String) -> (1 acc : String) -> String\n'
                        f'fold {names} items acc = case items of\n'
                        '  Data.Items.Empty => acc\n'
                        f'  Data.Items.Prepend head tail => fold {names} tail (appendString acc head)\n'
                        'main : IO Unit\nmain = putStrLn "checked"\n')
            path.write_text(program(64))
            admitted = run_cli('check', '--source-dir', str(root), str(path), timeout=120)
            self.assertEqual(admitted.returncode, 0, admitted.stdout + admitted.stderr)
            path.write_text(program(65))
            rejected = run_cli('check', '--source-dir', str(root), str(path), timeout=120)
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)

    def test_accumulator_first_rejects_dependent_types(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        examples = [
            ('data Indexed (0 key : String) : Type where\n  MkIndexed : Indexed key\n',
             '(1 acc : String) -> (1 items : Data.Items.Items (Indexed acc)) -> String',
             'acc', 'bad acc tail'),
            ('data Indexed (0 key : String) : Type where\n  MkIndexed : Indexed key\n',
             '(1 acc : String) -> (1 items : Data.Items.Items String) -> Indexed acc',
             'MkIndexed acc', 'bad acc tail')]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Dependent.fib'
            for declaration, signature, base, call in examples:
                preamble = 'module Dependent\nimport Data.Items\n' + declaration + '0 bad : ' + signature + '\n'
                main = 'main : IO Unit\nmain = putStrLn "checked"\n'
                path.write_text(preamble + 'bad acc items = ' + base + '\n' + main)
                baseline = run('check', '--source-dir', str(root), str(path))
                self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
                path.write_text(preamble + 'bad acc items = case items of\n'
                                '  Data.Items.Empty => ' + base + '\n'
                                '  Data.Items.Prepend head tail => ' + call + '\n' + main)
                rejected = run('check', '--source-dir', str(root), str(path))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                # Rejection now comes from the general recursion gate, not name resolution.
                self.assertIn('Recursion:', rejected.stderr)

    def test_general_recursion_is_admitted_by_size_change(self):
        root = ROOT / 'examples/modules/general-recursion'
        # Steps down by two, so no single-step recursor expresses it; the
        # predecessor of the predecessor is strictly smaller than the input.
        half = run('run', '--source-dir', str(root), str(root / 'Half.fib'))
        self.assertEqual(half.returncode, 0, half.stdout + half.stderr)
        self.assertEqual(half.stdout, '!!!\n')
        # Rebuilding the input in the recursive call decreases nothing.
        spin = run('check', '--source-dir', str(root), str(root / 'Loop.fib'))
        self.assertNotEqual(spin.returncode, 0, spin.stdout + spin.stderr)
        self.assertIn('Recursion:', spin.stderr)
        self.assertIn('no argument decreases', spin.stderr)
        self.assertIn('recursive call 1 of 1', spin.stderr)
        self.assertEqual(spin.stdout, '')
        # Swapping the arguments decreases neither alone; the composite of two calls does.
        drain = run('run', '--source-dir', str(root), str(root / 'Swap.fib'))
        self.assertEqual(drain.returncode, 0, drain.stdout + drain.stderr)
        self.assertEqual(drain.stdout, '!\n')
        # The unary recursive-data family steps down two links through the same gate.
        chain = run('run', '--source-dir', str(root), str(root / 'Chain.fib'))
        self.assertEqual(chain.returncode, 0, chain.stdout + chain.stderr)
        self.assertEqual(chain.stdout, 'xxx\n')
        # A helper built with natRec is inlined as a recursor term; calling it from a
        # recursive function is fine, so this is admitted and evaluates to 4.
        doubling = run('run', '--source-dir', str(root), str(root / 'Doubling.fib'))
        self.assertEqual(doubling.returncode, 0, doubling.stdout + doubling.stderr)
        self.assertEqual(doubling.stdout, '!!!!\n')
        # An unrestricted scrutinee gives an unrestricted predecessor, so a pattern
        # variable may be used twice: branching recursion (fib) and Ackermann.
        for name in ('Fibonacci', 'Ackermann'):
            unrestricted = run('run', '--source-dir', str(root), '--fuel', '4096', str(root / (name + '.fib')))
            self.assertEqual(unrestricted.returncode, 0, name + unrestricted.stdout + unrestricted.stderr)
            self.assertEqual(unrestricted.stdout, '!!!\n', name)
        # The same Fibonacci with a LINEAR parameter keeps the linear predecessor, which
        # cannot be used twice: the quantity of the scrutinee decides.
        with tempfile.TemporaryDirectory() as directory:
            linear = Path(directory) / 'Fibonacci.fib'
            linear.write_text((root / 'Fibonacci.fib').read_text().replace('fib : (n : Nat)', 'fib : (1 n : Nat)'))
            rejected = run('check', '--source-dir', directory, str(linear))
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
            self.assertIn('Binder usage', rejected.stderr)

    def test_run_fuel_option_raises_the_planning_budget(self):
        def nat(n):
            return 'Zero' if n == 0 else '(Succ ' * n + 'Zero' + ')' * n
        source = ('module Main\n'
                  'half : (1 n : Nat) -> Nat\nhalf n = case n of\n  Zero => Zero\n'
                  '  Succ a => case a of\n    Zero => Zero\n    Succ b => Succ (half b)\n'
                  'marks : (1 count : Nat) -> String\n'
                  'marks count = natRec (\\(0 k : Nat) => String) ""\n'
                  '  (\\(0 k : Nat) => \\(1 result : String) => appendString result "!") count\n'
                  'main : IO Unit\nmain = putStrLn (marks (half ' + nat(16) + '))\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Main.fib').write_text(source)
            entry = str(root / 'Main.fib')
            # The default budget is unchanged and too small for this recursion.
            default = run('run', '--source-dir', str(root), entry)
            self.assertNotEqual(default.returncode, 0, default.stdout)
            self.assertIn('IO planning reduction budget exhausted', default.stderr)
            self.assertIn('run --fuel N', default.stderr)
            # The explicit bound admits it; the answer is half of 16 marks.
            raised = run('run', '--source-dir', str(root), '--fuel', '4096', entry)
            self.assertEqual(raised.returncode, 0, raised.stdout + raised.stderr)
            self.assertEqual(raised.stdout, '!!!!!!!!\n')
            # Out-of-range and non-numeric bounds are rejected before anything runs.
            for bad in ['4097', 'x', '', '-1', '04096x']:
                rejected = run('run', '--source-dir', str(root), '--fuel', bad, entry)
                self.assertNotEqual(rejected.returncode, 0, bad)
                self.assertIn('Fuel must be decimal 0..4096', rejected.stderr)
                self.assertEqual(rejected.stdout, '')
            # A plain single-file program accepts the flag too.
            plain = root / 'plain.fib'
            plain.write_text('main : IO Unit\nmain = putStrLn "hi"\n')
            plain_run = run('run', '--fuel', '128', str(plain))
            self.assertEqual(plain_run.returncode, 0, plain_run.stdout + plain_run.stderr)
            self.assertEqual(plain_run.stdout, 'hi\n')

    def test_test_fuel_option_raises_the_suite_evaluation_budget(self):
        def nat(n):
            return 'Zero' if n == 0 else '(Succ ' * n + 'Zero' + ')' * n
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            created = run('new', 'mathlib', '--lib', cwd=root)
            self.assertEqual(created.returncode, 0, created.stdout + created.stderr)
            project = root / 'mathlib'
            (project / 'src/App.fib').write_text(
                'module App\n\nexport\nhalf : (1 n : Nat) -> Nat\nhalf n = case n of\n  Zero => Zero\n'
                '  Succ a => case a of\n    Zero => Zero\n    Succ b => Succ (half b)\n')
            suite = project / 'test/src/TestSuite/Suite.fib'
            def write(expect_nonzero):
                # half 1 is zero; half 24 is 12. The second conjunct forces real evaluation.
                second = '(notBool (isZero (App.half ' + nat(24) + ')))' if expect_nonzero \
                    else '(isZero (App.half ' + nat(24) + '))'
                suite.write_text(
                    'module TestSuite.Suite\nimport App\n\n'
                    'isZero : (n : Nat) -> Bool\nisZero n = case n of\n  Zero => True\n  Succ p => False\n\n'
                    'main : Bool\nmain = andBool (isZero (App.half (Succ Zero))) ' + second + '\n')
            write(True)
            # The default budget is unchanged and too small for this suite; the message says how to proceed.
            default = run('test', cwd=project)
            self.assertNotEqual(default.returncode, 0, default.stdout)
            self.assertIn('fuel exhausted (128)', default.stderr)
            self.assertIn('test --fuel N', default.stderr)
            # An explicit bound lets the same suite pass, in both the default and --package forms.
            for args in (('test', '--fuel', '4096'), ('test', '--package', str(project / 'fibril.yaml'), '--fuel', '4096')):
                passed = run(*args, cwd=project)
                self.assertEqual(passed.returncode, 0, passed.stdout + passed.stderr)
                self.assertIn('Tests: passed', passed.stdout)
            # More fuel must not turn a failing suite into a passing one.
            write(False)
            failed = run('test', '--fuel', '4096', cwd=project)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn('Tests: failed', failed.stderr)
            self.assertEqual(failed.stdout, '')
            # Out-of-range and non-numeric bounds are rejected before anything is evaluated.
            for bad in ['4097', 'x', '']:
                rejected = run('test', '--fuel', bad, cwd=project)
                self.assertNotEqual(rejected.returncode, 0, bad)
                self.assertIn('Fuel must be decimal 0..4096', rejected.stderr)

    def test_general_recursion_locations_and_navigation(self):
        root = ROOT / 'examples/modules/general-recursion'
        # A single refused call is reported at the call itself, not the declaration.
        loop = run('check', '--source-dir', str(root), str(root / 'Loop.fib'))
        self.assertNotEqual(loop.returncode, 0)
        self.assertIn('Loop.fib:7:13:', loop.stderr)
        self.assertIn('(at its recursive call)', loop.stderr)
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            def definition(path, line, column):
                result = run('definition', '--source-dir', directory, '--entry', str(path), str(line), str(column), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                found = json.loads(result.stdout)['definition']
                return None if found is None else (found['range']['start']['line'], found['range']['start']['column'])
            # With several refused calls the error stays at the declaration and lists them all.
            two = work / 'Two.fib'
            two.write_text('module Two\n\nspin : (1 n : Nat) -> Nat\nspin n = case n of\n'
                           '  Zero => spin Zero\n  Succ a => spin (Succ a)\n\nmain : IO Unit\nmain = putStrLn "x"\n')
            refused = run('check', '--source-dir', directory, str(two))
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn('Two.fib:3:1:', refused.stderr)
            self.assertIn('recursive calls at 5:11, 6:13', refused.stderr)
            self.assertNotIn('(at its recursive call)', refused.stderr)
            # An unrelated recursion error is not pinned on a call it has nothing to do with.
            unsupported = work / 'Unsupported.fib'
            unsupported.write_text('module Unsupported\n\nf : (1 n : IO Unit) -> IO Unit\nf n = f n\n\nmain : IO Unit\nmain = putStrLn "x"\n')
            other = run('check', '--source-dir', directory, str(unsupported))
            self.assertNotEqual(other.returncode, 0)
            self.assertIn('unsupported term form', other.stderr)
            self.assertNotIn('(at its recursive call)', other.stderr)
            # Definition navigation: an admitted recursive call resolves to the equation head.
            for name, call, head in (('Half', (10, 21), (6, 1)), ('Fibonacci', (14, 20), (10, 1))):
                source = (root / (name + '.fib')).read_text()
                copy = work / (name + '.fib')
                copy.write_text(source)
                self.assertEqual(definition(copy, *call), head, name)
            # A binder that shadows the function's name makes the token count disagree with the
            # checked call count, so no site is invented: the answer is null, never a wrong target.
            shadow = 'module Shadow\n\nh : (1 n : Nat) -> Nat\nh n = case n of\n  Zero => (\\(1 h : Nat) => h) Zero\n' \
                     '  Succ a => case a of\n    Zero => Zero\n    Succ b => Succ (h b)\n\nmain : IO Unit\nmain = putStrLn "ok"\n'
            (work / 'Shadow.fib').write_text(shadow)
            self.assertEqual(run('run', '--source-dir', directory, str(work / 'Shadow.fib')).stdout, 'ok\n')
            self.assertIsNone(definition(work / 'Shadow.fib', 8, 21))
            clean = shadow.replace('(\\(1 h : Nat) => h) Zero', 'Zero').replace('Shadow', 'Clean')
            (work / 'Clean.fib').write_text(clean)
            self.assertEqual(definition(work / 'Clean.fib', 8, 21), (4, 1))

    def test_numeric_literals_denote_builtin_nats(self):
        marks = ('marks : (1 count : Nat) -> String\n'
                 'marks count = natRec (\\(0 k : Nat) => String) ""\n'
                 '  (\\(0 k : Nat) => \\(1 result : String) => appendString result "!") count\n')
        def program(expression, extra=''):
            return 'module Main\n' + extra + marks + 'main : IO Unit\nmain = putStrLn ' + expression + '\n'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Main.fib'
            def go(source, *flags):
                path.write_text(source)
                return run('run', '--source-dir', directory, *flags, str(path))
            # A literal is an ordinary Nat expression, also as an application argument.
            ok = go(program('(marks 3)'))
            self.assertEqual((ok.returncode, ok.stdout), (0, '!!!\n'), ok.stderr)
            self.assertEqual(go(program('(marks 0)')).stdout, '\n')
            # Values far beyond the old nested-Succ parser limit are one token.
            big = go(program('(marks 200)'), '--fuel', '4096')
            self.assertEqual(big.returncode, 0, big.stdout + big.stderr)
            self.assertEqual(big.stdout, '!' * 200 + '\n')
            # The largest accepted literal is 256; larger and non-canonical spellings are rejected.
            self.assertEqual(go(program('(marks 256)'), '--fuel', '4096').returncode, 0)
            over = go(program('(marks 257)'))
            self.assertNotEqual(over.returncode, 0)
            self.assertIn('Numeric literal exceeds 256', over.stderr)
            zeros = go(program('(marks 007)'))
            self.assertNotEqual(zeros.returncode, 0)
            self.assertIn('leading zeros', zeros.stderr)
            # A literal has type Nat and nothing else.
            mismatch = go('module Main\nb : Bool\nb = 3\nmain : IO Unit\nmain = putStrLn "x"\n')
            self.assertNotEqual(mismatch.returncode, 0)
            self.assertIn('not compatible', mismatch.stderr)
            # A user binding of Zero or Succ cannot change what a literal means.
            shadowed = go(program('(marks 2)', 'Zero : Bool\nZero = True\n'))
            self.assertEqual((shadowed.returncode, shadowed.stdout), (0, '!!\n'), shadowed.stderr)
            # Literals are expressions; literal patterns are not supported.
            pattern = go('module Main\nf : (n : Nat) -> Bool\nf n = case n of\n  0 => True\n  Succ p => False\n'
                         'main : IO Unit\nmain = putStrLn "x"\n')
            self.assertNotEqual(pattern.returncode, 0)
            # Type levels and quantity binders keep their meaning.
            levels = go('module Main\nid : (0 A : Type 0) -> (1 x : A) -> A\nid A x = x\n'
                        'main : IO Unit\nmain = putStrLn (id String "ok")\n')
            self.assertEqual((levels.returncode, levels.stdout), (0, 'ok\n'), levels.stderr)
            # The formatter keeps the spelling and its structure guard accepts the result.
            path.write_text('module Main\n\nn : Nat\nn =   Succ   (Succ   12)\n\nm : Nat\nm = 256\n')
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn('n = Succ (Succ 12)', formatted.stdout)
            self.assertIn('m = 256', formatted.stdout)

    def test_compact_data_alternatives(self):
        source = (
            'module Main\n\n'
            'data Day = Monday\n         | Tuesday\n\n'
            'data User = Guest | Staff String | Customer String String\n\n'
            'data Tree = Leaf | Node Tree Tree\n\n'
            'data Items (0 A : Type) = Empty | Prepend A (Items A)\n\n'
            'name : (d : Day) -> String\nname d = case d of\n  Monday => "mon"\n  Tuesday => "tue"\n\n'
            'marks : (t : Tree) -> String\nmarks t = case t of\n  Leaf => "."\n'
            '  Node l r => appendString (marks l) (marks r)\n\n'
            'count : (0 A : Type) -> (xs : Items A) -> String\ncount A xs = case xs of\n  Empty => ""\n'
            '  Prepend x rest => appendString "!" (count A rest)\n\n'
            'who : (u : User) -> String\nwho u = case u of\n  Guest => "guest"\n  Staff e => e\n'
            '  Customer e p => p\n\n'
            'main : IO Unit\nmain = do\n  putStrLn (name Tuesday)\n  putStrLn (marks (Node (Node Leaf Leaf) Leaf))\n'
            '  putStrLn (count String (Prepend String "a" (Prepend String "b" (Empty String))))\n'
            '  putStrLn (who (Customer "c" "pw"))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def go(text, command='check'):
                path.write_text(text)
                args = ['--fuel', '4096'] if command == 'run' else []
                return run(command, '--source-dir', directory, *args, str(path))
            ran = go(source, 'run')
            self.assertEqual((ran.returncode, ran.stdout), (0, 'tue\n...\n!!\npw\n'), ran.stderr)
            formatted = run('format', '--check', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stdout + formatted.stderr)
            # The compact form reaches the same positivity gate as the where form.
            bad = go('module Main\n\ndata Bad = Wrap (Nat -> Bad)\n\nmain : IO Unit\nmain = putStrLn "x"\n')
            self.assertNotEqual(bad.returncode, 0)
            self.assertIn('under a function type', bad.stdout + bad.stderr)
            for text, message in (('data Bad = \n', 'Expected a constructor name'),
                                  ('data Bad = A | | B\n', 'Expected a constructor name'),
                                  ('data Bad = A (Nat\n', 'Unclosed parenthesis'),
                                  ('data Dup = A | A\n', 'Duplicate declaration')):
                failed = go('module Main\n\n' + text + '\nmain : IO Unit\nmain = putStrLn "x"\n')
                self.assertNotEqual(failed.returncode, 0, text)
                self.assertIn(message, failed.stdout + failed.stderr, text)

    def test_general_recursive_data(self):
        tree = ('module Main\n\ndata Tree : Type where\n  Leaf : Tree\n'
                '  Node : (left : Tree) -> (right : Tree) -> Tree\n\n')
        main = '\nmain : IO Unit\nmain = putStrLn (marks (Node (Node Leaf Leaf) Leaf))\n'
        marks = ('marks : (t : Tree) -> String\nmarks t = case t of\n  Leaf => "."\n'
                 '  Node l r => appendString (marks l) (marks r)\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def check(source, command='check'):
                path.write_text(source)
                args = ['--fuel', '4096'] if command == 'run' else []
                return run(command, '--source-dir', directory, *args, str(path))
            # A tree, not one of the two fixed shapes, declares, recurses on both subtrees and runs.
            ran = check(tree + marks + main, 'run')
            self.assertEqual((ran.returncode, ran.stdout), (0, '...\n'), ran.stderr)
            example = ROOT / 'examples/modules/general-data'
            shipped = run('run', '--source-dir', str(example), '--fuel', '4096', str(example / 'Main.fib'))
            self.assertEqual((shipped.returncode, shipped.stdout), (0, '...\n(b(bb))\n'), shipped.stderr)
            # A parameterized family, with the parameter passed explicitly to its constructors.
            rose = ('module Main\n\ndata Rose (0 A : Type) : Type where\n  Bud : (value : A) -> Rose A\n'
                    '  Branch : (value : A) -> (first : Rose A) -> (second : Rose A) -> Rose A\n\n'
                    'size : (t : Rose Nat) -> String\nsize t = case t of\n  Bud v => "b"\n'
                    '  Branch v a b => appendString "n" (appendString (size a) (size b))\n\n'
                    'main : IO Unit\nmain = putStrLn (size (Branch Nat Zero (Bud Nat Zero) (Bud Nat Zero)))\n')
            rose_run = check(rose, 'run')
            self.assertEqual((rose_run.returncode, rose_run.stdout), (0, 'nbb\n'), rose_run.stderr)
            # A family crosses a module boundary with its constructors, and an imported recursive
            # function over it still runs. Two modules may each declare a `Tree`: the keys differ.
            (Path(directory) / 'Data').mkdir()
            shapes = ('module Data.Shapes\n\nexport\ndata Tree : Type where\n  Leaf : Tree\n'
                      '  Node : (left : Tree) -> (right : Tree) -> Tree\n\nexport\nmarks : (t : Tree) -> String\n'
                      'marks t = case t of\n  Leaf => "."\n  Node l r => appendString (marks l) (marks r)\n')
            (Path(directory) / 'Data' / 'Shapes.fib').write_text(shapes)
            importer = ('module Main\n\nimport Data.Shapes\n\n'
                        'depth : (t : Data.Shapes.Tree) -> String\ndepth t = case t of\n  Data.Shapes.Leaf => "L"\n'
                        '  Data.Shapes.Node l r => appendString "(" (appendString (depth l) (appendString (depth r) ")"))\n\n'
                        'main : IO Unit\nmain = do\n'
                        '  putStrLn (Data.Shapes.marks (Data.Shapes.Node Data.Shapes.Leaf Data.Shapes.Leaf))\n'
                        '  putStrLn (depth (Data.Shapes.Node Data.Shapes.Leaf (Data.Shapes.Node Data.Shapes.Leaf Data.Shapes.Leaf)))\n')
            imported = check(importer, 'run')
            self.assertEqual((imported.returncode, imported.stdout), (0, '..\n(L(LL))\n'), imported.stderr)
            # The imported family is not the local one with the same name.
            clash = check('module Main\n\nimport Data.Shapes\n\ndata Tree : Type where\n  Leaf : Tree\n'
                          '  Node : (left : Tree) -> (right : Tree) -> Tree\n\n'
                          'mix : (t : Main.Tree) -> String\nmix t = Data.Shapes.marks t\n\n'
                          'main : IO Unit\nmain = putStrLn "x"\n')
            self.assertNotEqual(clash.returncode, 0)
            self.assertIn('not compatible', clash.stderr)
            # Recursion that does not shrink is refused by the same gate as other recursion.
            for body in ('Node l r => marks (Node l r)', 'Node l r => marks t'):
                refused = check(tree + 'marks : (t : Tree) -> String\nmarks t = case t of\n  Leaf => "."\n  '
                                + body + '\n' + main)
                self.assertNotEqual(refused.returncode, 0, body)
                self.assertIn('no argument decreases', refused.stderr)
            # Clause equations recurse over a family exactly like the case form.
            clauses = ('marks : (t : Tree) -> String\nmarks Leaf = "."\n'
                       'marks (Node l r) = appendString (marks l) (marks r)\n')
            by_clauses = check(tree + clauses + main, 'run')
            self.assertEqual((by_clauses.returncode, by_clauses.stdout), (0, '...\n'), by_clauses.stderr)
            clause_rose = ('module Main\n\ndata Rose (0 A : Type) : Type where\n  Bud : (value : A) -> Rose A\n'
                           '  Branch : (value : A) -> (first : Rose A) -> (second : Rose A) -> Rose A\n\n'
                           'size : (t : Rose Nat) -> String\nsize (Bud v) = "b"\n'
                           'size (Branch v a b) = appendString "n" (appendString (size a) (size b))\n\n'
                           'main : IO Unit\nmain = putStrLn (size (Branch Nat Zero (Bud Nat Zero) (Bud Nat Zero)))\n')
            rose_clauses = check(clause_rose, 'run')
            self.assertEqual((rose_clauses.returncode, rose_clauses.stdout), (0, 'nbb\n'), rose_clauses.stderr)
            # A recursive clause that does not shrink is refused by the termination gate.
            for call in ('marks (Node l r)', 'marks (Node r l)'):
                spinning = check(tree + 'marks : (t : Tree) -> String\nmarks Leaf = "."\n'
                                 'marks (Node l r) = ' + call + '\n' + main)
                self.assertNotEqual(spinning.returncode, 0, call)
                self.assertIn('no argument decreases', spinning.stderr)
            # A clause pattern may not bind the function's own name.
            named = check(tree + 'marks : (t : Tree) -> String\nmarks Leaf = "."\n'
                          'marks (Node marks r) = "x"\n' + main)
            self.assertNotEqual(named.returncode, 0)
            self.assertIn("own name", named.stderr)
            # Recursion through a type the extractor cannot see is refused with a hint.
            flag = ('module Main\n\ndata Flag : Type where\n  On : Flag\n  Off : Flag\n\n'
                    'spin : (f : Flag) -> String\nspin On = "on"\nspin Off = spin Off\n\n'
                    'main : IO Unit\nmain = putStrLn "x"\n')
            refused_flag = check(flag)
            self.assertNotEqual(refused_flag.returncode, 0)
            self.assertIn('general recursive data', refused_flag.stderr)
            # A recursive field under a function type is not strictly positive.
            negative = check('module Main\n\ndata Bad : Type where\n  Leaf : Bad\n'
                             '  Wrap : (child : (n : Nat) -> Bad) -> Bad\n\nmain : IO Unit\nmain = putStrLn "x"\n')
            self.assertNotEqual(negative.returncode, 0)
            self.assertIn('under a function type', negative.stderr)
            # A case must cover every constructor and bind exactly its fields.
            missing = check(tree + 'marks : (t : Tree) -> String\nmarks t = case t of\n  Leaf => "."\n' + main)
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn('every constructor', missing.stderr)
            arity = check(tree + 'marks : (t : Tree) -> String\nmarks t = case t of\n  Leaf => "."\n'
                          '  Node l => "x"\n' + main)
            self.assertNotEqual(arity.returncode, 0)
            self.assertIn('fields', arity.stderr)

    def test_general_mutual_groups(self):
        root = ROOT / 'examples/modules/general-recursion'
        # Two members over user data, and a three-member ring with two parameters: both are outside
        # the bounded Nat/Bool form and are checked by the ordinary size-change gate.
        chain = run('run', '--source-dir', str(root), '--fuel', '4096', str(root / 'MutualChain.fib'))
        self.assertEqual(chain.returncode, 0, chain.stdout + chain.stderr)
        self.assertEqual(chain.stdout, 'zero links: even\ntwo links: even\nthree links: odd\n')
        ring = run('run', '--source-dir', str(root), '--fuel', '4096', str(root / 'MutualRing.fib'))
        self.assertEqual(ring.returncode, 0, ring.stdout + ring.stderr)
        self.assertEqual(ring.stdout, '.\nrgbrg.\nbr.\n')
        forward = run('run', '--source-dir', str(root), '--fuel', '4096', str(root / 'MutualForward.fib'))
        self.assertEqual((forward.returncode, forward.stdout), (0, '.\nststst.\n'), forward.stderr)
        header = 'module Main\n\ndata Chain : Type where\n  Empty : Chain\n  More : (1 tail : Chain) -> Chain\n\n'
        tail = '\nmain : IO Unit\nmain = putStrLn "x"\n'
        def member(name, nxt, arm='Empty => True', result='Bool'):
            return (f'  {name} : (1 c : Chain) -> {result}\n  {name} c = case c of\n    {arm}\n'
                    f'    More r => {nxt}\n\n')
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            path = work / 'Main.fib'
            def check(source):
                path.write_text(source)
                return run('check', '--source-dir', directory, str(path))
            # A member may merely forward its argument when another member in the cycle shrinks it.
            def counting(second):
                return ('module Main\n\nmutual where\n'
                        '  isEven : (c : Nat) -> String\n  isEven c = case c of\n    Zero => "even"\n    Succ r => isOdd c\n\n'
                        '  isOdd : (c : Nat) -> String\n  isOdd c = case c of\n    Zero => "odd"\n'
                        f'    Succ r => {second}\n\nmain : IO Unit\nmain = putStrLn (isEven 4)\n')
            forwarding = check(counting('isEven r'))
            self.assertEqual(forwarding.returncode, 0, forwarding.stdout + forwarding.stderr)
            ran = run('run', '--source-dir', directory, '--fuel', '4096', str(path))
            self.assertEqual((ran.returncode, ran.stdout), (0, 'even\n'), ran.stderr)
            # A cycle in which nothing shrinks is refused, whatever the group shape.
            refused = check(counting('isEven c'))
            self.assertNotEqual(refused.returncode, 0)
            self.assertIn('no argument decreases', refused.stderr)
            self.assertIn('cycle', refused.stderr)
            # Every call rebuilding its input is refused too.
            rebuilt = check(header + 'mutual where\n' + member('isEven', 'isOdd (More r)') + member('isOdd', 'isEven (More r)', 'Empty => False') + tail)
            self.assertNotEqual(rebuilt.returncode, 0)
            # Members must share one signature; the error names the group.
            different = check(header + 'mutual where\n' + member('isEven', 'isOdd r') +
                              '  isOdd : (1 c : Chain) -> String\n  isOdd c = case c of\n    Empty => "n"\n    More r => "m"\n\n' + tail)
            self.assertNotEqual(different.returncode, 0)
            self.assertIn('must share one signature', different.stderr)
            self.assertNotIn('Unbound', different.stderr)
            # Up to eight members are accepted; a ring that long runs.
            eight = ''.join(member(f'm{i}', f'm{(i + 1) % 8} r') for i in range(8))
            ring8 = check(header + 'mutual where\n' + eight + tail)
            self.assertEqual(ring8.returncode, 0, ring8.stdout + ring8.stderr)
            # At most eight members.
            nine = ''.join(member(f'm{i}', f'm{(i + 1) % 9} r') for i in range(9))
            over = check(header + 'mutual where\n' + nine + tail)
            self.assertNotEqual(over.returncode, 0)
            self.assertIn('at most eight', over.stderr)
            # Members must be equations that name their parameters as the signature does.
            lam = check(header + 'mutual where\n  isEven : (1 c : Chain) -> Bool\n  isEven = \\(1 c : Chain) => True\n\n' + member('isOdd', 'isEven r', 'Empty => False') + tail)
            self.assertNotEqual(lam.returncode, 0)
            self.assertIn('function equations', lam.stderr)
            renamed = check(header + 'mutual where\n  isEven : (1 c : Chain) -> Bool\n  isEven d = case d of\n    Empty => True\n    More r => isOdd r\n\n' + member('isOdd', 'isEven r', 'Empty => False') + tail)
            self.assertNotEqual(renamed.returncode, 0)
            self.assertIn('name their parameters', renamed.stderr)
            # A plain Nat/Bool pair whose first member only forwards is a general group too.
            def alias(second):
                return ('module Main\n\nmutual where\n  start : (1 n : Nat) -> Bool\n  start n = step n\n\n'
                        f'  step : (1 n : Nat) -> Bool\n  step n = case n of\n    Zero => True\n    Succ p => {second}\n'
                        '\nmain : IO Unit\nmain = putStrLn (if start 3 then "yes" else "no")\n')
            aliased = check(alias('start p'))
            self.assertEqual(aliased.returncode, 0, aliased.stdout + aliased.stderr)
            self.assertEqual(run('run', '--source-dir', directory, '--fuel', '4096', str(path)).stdout, 'yes\n')
            spinning = check(alias('start (Succ p)'))
            self.assertNotEqual(spinning.returncode, 0)
            self.assertIn('no argument decreases', spinning.stderr)
            # The bounded Nat/Bool pair keeps its own lowering and its own diagnostics.
            nat_bool = work / 'Parity.fib'
            nat_bool.write_text('module Parity\n\nmutual where\n  isEven : (1 n : Nat) -> Bool\n  isEven n = case n of\n'
                                '    Zero => True\n    Succ p => isOdd p\n\n  isOdd : (1 n : Nat) -> Bool\n  isOdd n = case n of\n'
                                '    Zero => False\n    Succ p => isEven p\n\nmain : IO Unit\nmain = putStrLn (if isEven 4 then "even" else "odd")\n')
            bounded = run('run', '--source-dir', directory, str(nat_bool))
            self.assertEqual((bounded.returncode, bounded.stdout), (0, 'even\n'), bounded.stderr)
            # The formatter keeps all members and its structure guard covers the extra ones.
            ring_path = work / 'MutualRing.fib'
            ring_path.write_text((root / 'MutualRing.fib').read_text())
            formatted = run('format', str(ring_path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            for name in ('red', 'green', 'blue'):
                self.assertIn(f'  {name} : (1 c : Chain)', formatted.stdout)
            # Navigation reaches a member from a call in another member, including the third.
            ring_text = (root / 'MutualRing.fib').read_text()
            lines = ring_text.split('\n')
            call = next(i for i, l in enumerate(lines, 1) if 'blue rest' in l)
            column = lines[call - 1].index('blue') + 1
            located = run('definition', '--source-dir', directory, '--entry', str(ring_path), str(call), str(column), str(ring_path))
            self.assertEqual(located.returncode, 0, located.stdout + located.stderr)
            target = json.loads(located.stdout)['definition']['range']['start']
            self.assertEqual(lines[target['line'] - 1].split()[0], 'blue')
            # A recursive function with a real type error reports it, not an unbound recursive name.
            wrong = check('module Main\n\nhalf : (1 n : Nat) -> Nat\nhalf n = case n of\n  Zero => "text"\n'
                          '  Succ a => case a of\n    Zero => Zero\n    Succ b => Succ (half b)\n' + tail)
            self.assertNotEqual(wrong.returncode, 0)
            self.assertNotIn('Unbound name "half"', wrong.stderr)

    def test_accumulator_equations_reject_dependent_types(self):
        fixture = ROOT / 'examples/modules/linear-accumulator'
        examples = [
            ('data IndexedList (0 tag : Data.Items.Items String) : Type where\n'
             '  MkIndexedList : IndexedList tag\n',
             '(1 items : Data.Items.Items String) -> (1 acc : IndexedList items) -> IndexedList items',
             'acc', 'bad tail acc'),
            ('data Indexed (0 tag : String) : Type where\n  MkIndexed : Indexed tag\n',
             '(1 items : Data.Items.Items String) -> (1 acc : String) -> Indexed acc',
             'MkIndexed acc', 'bad tail (appendString acc head)')]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture / 'Data', root / 'Data')
            path = root / 'Dependent.fib'
            for declaration, signature, base, call in examples:
                preamble = 'module Dependent\nimport Data.Items\n' + declaration + '0 bad : ' + signature + '\n'
                main = 'main : IO Unit\nmain = putStrLn "checked"\n'
                path.write_text(preamble + 'bad items acc = ' + base + '\n' + main)
                baseline = run('check', '--source-dir', str(root), str(path))
                self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
                path.write_text(preamble + 'bad items acc = case items of\n'
                                '  Data.Items.Empty => ' + base + '\n'
                                '  Data.Items.Prepend head tail => ' + call + '\n' + main)
                rejected = run('check', '--source-dir', str(root), str(path))
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                # A dependent result needs an explicit motive; the real reason is reported,
                # not a phantom unbound name for the recursive function itself.
                self.assertIn('motive', rejected.stderr)
                self.assertNotIn('Unbound', rejected.stderr)

    def test_structural_sequence_recursive_equations(self):
        source = ('module Main\ndata Items {0 A : Type} : Type where\n  Empty : Items A\n'
                  '  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                  'join : (1 xs : Items String) -> String\njoin xs = case xs of\n'
                  '  Empty => ""\n  Prepend head tail => appendString head (join tail)\n'
                  'main : IO Unit\nmain = putStrLn (join (Prepend "a" (Prepend "b" (Empty {String}))))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'ab\n')
            path.write_text(source.replace('join (Prepend "a" (Prepend "b" (Empty {String})))', 'join (Empty {String})'))
            self.assertEqual(project('run').stdout, '\n')
            reversed_arms = source.replace('  Empty => ""\n  Prepend head tail => appendString head (join tail)',
                                           '  Prepend head tail => appendString head (join tail)\n  Empty => ""')
            path.write_text(reversed_arms)
            self.assertEqual(project('run').stdout, 'ab\n')
            aliases = ('nilAlias : Items String\nnilAlias = Empty {String}\n'
                       'consAlias : (1 h : String) -> (1 t : Items String) -> Items String\n'
                       'consAlias h t = Prepend h t\n')
            path.write_text(source.replace('join :', aliases + 'join :').replace('  Empty =>', '  nilAlias =>').replace('  Prepend head tail =>', '  consAlias head tail =>'))
            self.assertEqual(project('run').stdout, 'ab\n')
            shadow = source.replace('join :', 'head : String\nhead = "base"\njoin :').replace('  Empty => ""', '  Empty => head')
            path.write_text(shadow)
            self.assertEqual(project('run').stdout, 'abbase\n')
            flags = ('module Main\ndata Items {0 A : Type} : Type where\n  Empty : Items A\n'
                     '  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                     'render : (1 flag : Bool) -> String\nrender flag = if flag then "T" else "F"\n'
                     'flags : (1 xs : Items Bool) -> String\nflags xs = case xs of\n  Empty => ""\n'
                     '  Prepend head tail => appendString (render head) (flags tail)\n'
                     'main : IO Unit\nmain = putStrLn (flags (Prepend True (Prepend False (Empty {Bool}))))\n')
            path.write_text(flags)
            self.assertEqual(project('run').stdout, 'TF\n')
            explicit = source.replace('{0 A : Type}', '(0 A : Type)').replace('Prepend "a"', 'Prepend String "a"').replace('Prepend "b"', 'Prepend String "b"').replace('Empty {String}', 'Empty String')
            path.write_text(explicit)
            self.assertEqual(project('run').stdout, 'ab\n')
            erased = source.replace('join :', '0 join :').replace('main = putStrLn (join (Prepend "a" (Prepend "b" (Empty {String}))))', 'main = putStrLn "erased"')
            path.write_text(erased)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'erased\n')
            bad_param = 'fake : (0 flag : Bool) -> Items String\nfake flag = Empty {String}\n'
            other = ('data Other {0 A : Type} : Type where\n  None : Other A\n'
                     '  Next : (1 head : A) -> (1 tail : Other A) -> Other A\n')
            invalid = [source.replace('appendString head (join tail)', 'join tail'),
                       source.replace('appendString head (join tail)', 'appendString head (appendString head (join tail))'),
                       source.replace('(join tail)', '(join xs)'),
                       source.replace('(join tail)', '(join (Prepend head tail))'),
                       source.replace('appendString head (join tail)', 'appendString (join tail) (join tail)'),
                       source.replace('  Empty => ""', '  Empty => join (Empty {String})'),
                       source.replace('appendString head (join tail)', 'if True then appendString head (join tail) else head'),
                       source.replace('Prepend head tail =>', 'Prepend tail tail =>'),
                       source.replace('join : (1 xs : Items String)', 'join : (xs : Items String)'),
                       source.replace('join :', bad_param + 'join :').replace('  Empty =>', '  fake =>'),
                       source.replace('join :', other + 'join :').replace('  Prepend head tail =>', '  Next head tail =>')]
            for program in invalid:
                with self.subTest(program=program[-150:]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            dependent = ('module Main\ndata Items {0 A : Type} : Type where\n  Empty : Items A\n'
                         '  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                         'data Tagged (0 xs : Items String) : Type where\n  Tag : Tagged xs\n'
                         'nil : Items String\nnil = Empty {String}\n'
                         'build : (1 xs : Items String) -> Tagged xs\nbuild xs = case xs of\n'
                         '  Empty => Tag nil\n  Prepend head tail => build tail\n'
                         'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(dependent)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('result independent', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # Keep this an actual conversion-budget test with shared bodies.
            expression = 'Prepend h t'
            for _ in range(50):
                expression = 'identity (' + expression + ')'
            large = ('identity : (1 value : Items String) -> Items String\nidentity value = let (1 copy : Items String) = value in copy\n'
                     'large : (1 h : String) -> (1 t : Items String) -> Items String\nlarge h t = ' + expression + '\n')
            guarded = source.replace('join :', large + 'join :').replace('  Prepend head tail =>', '  large head tail =>')
            path.write_text(guarded)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            path.write_text(guarded.replace('  large head tail =>', '  Prepend head tail =>'))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'ab\n')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'ab\n')

    def test_structural_unary_recursive_equations(self):
        source = ('module Main\ndata Chain : Type where\n  Empty : Chain\n'
                  '  More : (1 rest : Chain) -> Chain\n'
                  'marks : (1 chain : Chain) -> String\nmarks chain = case chain of\n'
                  '  Empty => ""\n  More rest => appendString "!" (marks rest)\n'
                  'main : IO Unit\nmain = putStrLn (marks (More (More Empty)))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '!!\n')
            path.write_text(source.replace('marks (More (More Empty))', 'marks Empty'))
            self.assertEqual(project('run').stdout, '\n')
            path.write_text(source.replace('  Empty => ""\n  More rest => appendString "!" (marks rest)',
                                           '  More rest => appendString "!" (marks rest)\n  Empty => ""'))
            self.assertEqual(project('run').stdout, '!!\n')
            alias = ('Done : Chain\nDone = Empty\nNext : (1 tail : Chain) -> Chain\nNext tail = More tail\n')
            path.write_text(source.replace('marks :', alias + 'marks :').replace('  Empty =>', '  Done =>').replace('  More rest =>', '  Next rest =>'))
            self.assertEqual(project('run').stdout, '!!\n')
            alias_type = source.replace('marks :', '0 Alias : Type\nAlias = Chain\nmarks :').replace('marks : (1 chain : Chain)', 'marks : (1 chain : Alias)')
            path.write_text(alias_type)
            self.assertEqual(project('run').stdout, '!!\n')
            erased = source.replace('marks :', '0 marks :').replace('main = putStrLn (marks (More (More Empty)))', 'main = putStrLn "erased"')
            path.write_text(erased)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'erased\n')
            foreign = ('data Other : Type where\n  Stop : Other\n  Next : (1 rest : Other) -> Other\n')
            invalid = [source.replace('(marks rest)', '(marks chain)'),
                       source.replace('(marks rest)', '(marks (More rest))'),
                       source.replace('appendString "!" (marks rest)', 'appendString (marks rest) (marks rest)'),
                       source.replace('  Empty => ""', '  Empty => marks Empty'),
                       source.replace('appendString "!" (marks rest)', 'if True then marks rest else ""'),
                       source.replace('  More rest => appendString "!" (marks rest)', '  More rest => appendString (marks rest) (marks rest)'),
                       source.replace('  More rest =>', '  More marks =>'),
                       source.replace('marks : (1 chain : Chain)', 'marks : (chain : Chain)'),
                       source.replace('marks :', foreign + 'marks :').replace('  More rest =>', '  Next rest =>')]
            for program in invalid:
                with self.subTest(program=program[-160:]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            # Dependent result types are not silently approximated by a
            # constant fold motive.
            dependent = ('module Main\ndata Chain : Type where\n  Empty : Chain\n'
                         '  More : (1 tail : Chain) -> Chain\n'
                         'data Tagged (0 value : Chain) : Type where\n  Tag : Tagged value\n'
                         'build : (1 chain : Chain) -> Tagged chain\nbuild chain = case chain of\n'
                         '  Empty => Tag Empty\n  More rest => build rest\n'
                         'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(dependent)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('result independent', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # An oversized transparent alias cannot serve as constructor evidence.
            # Shared bodies fit the syntax cap; spend an extra local beta step
            # per call to test conversion exhaustion below the parser depth cap.
            expression = 'More value'
            for _ in range(50):
                expression = 'identity (' + expression + ')'
            large = ('identity : (1 value : Chain) -> Chain\nidentity value = let (1 copy : Chain) = value in copy\n'
                     'large : (1 value : Chain) -> Chain\nlarge value = ' + expression + '\n')
            guarded = source.replace('marks :', large + 'marks :').replace('  More rest =>', '  large rest =>')
            path.write_text(guarded)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            path.write_text(guarded.replace('  large rest =>', '  More rest =>'))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '!!\n')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, '!!\n')

    def test_direct_sequence_cases(self):
        source = ('module Main\ndata Items {0 A : Type} : Type where\n  eliminator foldItems\n'
                  '  Empty : Items A\n  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                  'join : (1 xs : Items String) -> String\njoin xs = case xs of\n'
                  '  Empty => "empty"\n  Prepend head tail => appendString head '
                  '(foldItems String (\\(0 ys : Items String) => String) "!" '
                  '(\\(1 item : String) => \\(0 rest : Items String) => \\(1 result : String) => appendString item result) tail)\n'
                  'main : IO Unit\nmain = putStrLn (join (Prepend "a" (Prepend "b" (Empty {String}))))\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            checked = project('run')
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertEqual(checked.stdout, 'ab!\n')
            lines = source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if 'Prepend head tail =>' in line)
            line = lines[row - 1]
            for binder, use in [('head', line.index('appendString head') + len('appendString ')),
                                ('tail', line.rindex('tail)'))]:
                nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(use + 1), str(path))
                self.assertEqual(nav.returncode, 0, nav.stderr)
                start = json.loads(nav.stdout)['definition']['range']['start']
                self.assertEqual((start['line'], start['column']), (row, line.index(binder) + 1))
            generic = ('identity : (0 A : Type) -> (1 xs : Items A) -> Items A\n'
                       'identity A xs = case xs of\n  Empty => Empty {A}\n'
                       '  Prepend head tail => Prepend head tail\n')
            path.write_text(source.replace('join :', generic + 'join :').replace('join (Prepend "a"', 'join (identity String (Prepend "a"').replace('(Empty {String}))))', '(Empty {String})))))'))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'ab!\n')
            path.write_text(source.replace('case xs of', 'case xs return (\\(0 ys : Items String) => String) of'))
            self.assertEqual(project('run').stdout, 'ab!\n')
            path.write_text(source.replace('Prepend "a" (Prepend "b" (Empty {String}))', 'Empty {String}'))
            self.assertEqual(project('run').stdout, 'empty\n')
            # Transparent specialized aliases are accepted, but parameterized
            # aliases must accept the actual element type before instantiation.
            aliases = ('nilAlias : Items String\nnilAlias = Empty {String}\n'
                       'consAlias : (1 h : String) -> (1 t : Items String) -> Items String\n'
                       'consAlias h t = Prepend h t\n')
            aliased = source.replace('join :', aliases + 'join :').replace('  Empty =>', '  nilAlias =>').replace('  Prepend head tail =>', '  consAlias head tail =>')
            path.write_text(aliased)
            self.assertEqual(project('run').stdout, 'ab!\n')
            bad_alias = ('fake : (0 flag : Bool) -> Items String\nfake flag = Empty {String}\n')
            path.write_text(source.replace('join :', bad_alias + 'join :').replace('  Empty =>', '  fake =>'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('parameter cannot accept', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            foreign = ('data Other {0 A : Type} : Type where\n  None : Other A\n'
                       '  Next : (1 head : A) -> (1 tail : Other A) -> Other A\n')
            wrong_type = ('wrong : Items Bool\nwrong = Empty {Bool}\n')
            invalid = [source.replace('appendString head (foldItems', 'appendString "dropped" (foldItems'),
                       source.replace('appendString head (foldItems', 'appendString head (appendString head (foldItems').replace(') tail)\nmain', ') tail))\nmain'),
                       source.replace(') tail)\nmain', ') (Empty {String}))\nmain'),
                       source.replace('  Prepend head tail =>', '  Prepend head =>'),
                       source.replace('  Prepend head tail =>', '  Prepend head tail extra =>'),
                       source.replace('  Empty => "empty"', '  Empty => "empty"\n  Empty => "duplicate"'),
                       source.replace('join :', foreign + 'join :').replace('  Prepend head tail =>', '  Next head tail =>'),
                       source.replace('join :', wrong_type + 'join :').replace('  Empty =>', '  wrong =>')]
            for program in invalid:
                with self.subTest(program=program[-200:]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            dependent = ('module Main\ndata Items {0 A : Type} : Type where\n  eliminator foldItems\n'
                         '  Empty : Items A\n  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                         'data Tagged (0 xs : Items String) : Type where\n  Bad : Tagged xs\n'
                         '  Marked : (1 text : String) -> Tagged xs\n'
                         'build : (1 xs : Items String) -> Tagged xs\nbuild xs = case xs of\n'
                         '  Empty => Marked (Empty {String}) "empty"\n'
                         '  Prepend head tail => Marked (Prepend head tail) (appendString head '
                         '(foldItems String (\\(0 ys : Items String) => String) "!" '
                         '(\\(1 item : String) => \\(0 rest : Items String) => \\(1 result : String) => appendString item result) tail))\n'
                         'show : (0 xs : Items String) -> (1 value : Tagged xs) -> String\n'
                         'show xs value = case value of\n  Bad => "bad"\n  Marked text => text\n'
                         'main : IO Unit\nmain = putStrLn (show (Prepend "a" (Empty {String})) (build (Prepend "a" (Empty {String}))))\n')
            path.write_text(dependent)
            checked = project('run')
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertEqual(checked.stdout, 'a!\n')
            path.write_text(dependent.replace('case xs of', 'case xs return (\\(0 ys : Items String) => Tagged ys) of'))
            self.assertEqual(project('run').stdout, 'a!\n')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'ab!\n')

    def test_parameterized_recursive_list(self):
        import shutil
        fixture = ROOT / 'examples/modules/recursive-list'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture, root, dirs_exist_ok=True)
            path, library = root / 'Main.fib', root / 'Data/Items.fib'
            source, authored = path.read_text(), library.read_text()
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'hello world\n')
            lines = source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if 'Data.Items.Prepend' in line)
            col = lines[row - 1].index('Data.Items.Prepend') + len('Data.Items.') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(Path(json.loads(nav.stdout)['definition']['path']).name, 'Items.fib')
            path.write_text(source.replace('Data.Items.', ''))
            self.assertEqual(project('run').stdout, 'hello world\n')
            path.write_text(source)
            for file in [path, library]:
                formatted = run('format', str(file))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                file.write_text(formatted.stdout)
                self.assertEqual(run('format', '--check', str(file)).returncode, 0)
            self.assertEqual(project('run').stdout, 'hello world\n')
            # Parenthesized parameters preserve explicit constructor arguments.
            library.write_text(authored.replace('{0 A : Type}', '(0 A : Type)'))
            explicit = source.replace('Data.Items.Prepend "hello"', 'Data.Items.Prepend String "hello"')
            explicit = explicit.replace('Data.Items.Prepend " world"', 'Data.Items.Prepend String " world"').replace('Data.Items.Empty {String}', 'Data.Items.Empty String')
            path.write_text(explicit)
            self.assertEqual(project('run').stdout, 'hello world\n')
            # Reversed constructors and a qualified direct self type are safe.
            reversed_order = authored.replace('  Empty : Items A\n  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A',
                                               '  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n  Empty : Items A')
            library.write_text(reversed_order.replace('(1 tail : Items A)', '(1 tail : Data.Items.Items A)'))
            path.write_text(source)
            self.assertEqual(project('run').stdout, 'hello world\n')
            library.write_text(authored.replace('export\ndata Items', 'data Items'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            library.write_text(authored)
            bool_program = ('module Main\nimport Data.Items\n'
                            'flags : (1 xs : Data.Items.Items Bool) -> String\n'
                            'flags xs = Data.Items.foldItems Bool (\\(0 self : Data.Items.Items Bool) => String) "" '
                            '(\\(1 head : Bool) => \\(0 tail : Data.Items.Items Bool) => \\(1 result : String) => '
                            'if head then appendString "T" result else appendString "F" result) xs\n'
                            'main : IO Unit\nmain = putStrLn (flags (Data.Items.Prepend True '
                            '(Data.Items.Prepend False (Data.Items.Empty {Bool}))))\n')
            path.write_text(bool_program)
            boolean = project('run')
            self.assertEqual(boolean.returncode, 0, boolean.stdout + boolean.stderr)
            self.assertEqual(boolean.stdout, 'TF\n')
            path.write_text(source)
            dependency, client = root / 'dependency', root / 'client'
            (dependency / 'src/Data').mkdir(parents=True)
            (dependency / 'src/Data/Items.fib').write_text(authored)
            (dependency / 'fibril.yaml').write_text('schema: 1\nname: items-lib\nmodule-prefix: Data.Items\nsource-dir: src\nfoundation: de-morgan\nmodules: [Data.Items]\ndependencies: {}\n')
            (client / 'src').mkdir(parents=True)
            (client / 'src/Main.fib').write_text(source)
            (client / 'fibril.yaml').write_text('schema: 1\nname: items-client\nmodule-prefix: Demo\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  items-lib:\n    path: ../dependency\n')
            packaged = run('run', '--package', str(client / 'fibril.yaml'))
            self.assertEqual(packaged.returncode, 0, packaged.stdout + packaged.stderr)
            self.assertEqual(packaged.stdout, 'hello world\n')
            # The generated fold preserves a motive indexed by the actual list
            # and gives its step an erased tail and linear head/induction result.
            dependent = ('module Main\ndata Items {0 A : Type} : Type where\n  eliminator foldItems\n'
                         '  Empty : Items A\n  Prepend : (1 head : A) -> (1 tail : Items A) -> Items A\n'
                         'data Tagged (0 xs : Items String) : Type where\n  Bad : Tagged xs\n'
                         '  Marked : (1 text : String) -> Tagged xs\n'
                         'build : (1 xs : Items String) -> Tagged xs\n'
                         'build xs = foldItems String (\\(0 ys : Items String) => Tagged ys) (Marked (Empty {String}) "") '
                         '(\\(1 head : String) => \\(0 tail : Items String) => \\(1 prev : Tagged tail) => case prev of\n'
                         '  Bad => Marked (Prepend {String} head tail) head\n'
                         '  Marked text => Marked (Prepend {String} head tail) (appendString head text)) xs\n'
                         'show : (0 xs : Items String) -> (1 value : Tagged xs) -> String\n'
                         'show xs value = case value of\n  Bad => "bad"\n  Marked text => text\n'
                         'main : IO Unit\nmain = putStrLn (show (Prepend "a" (Empty {String})) (build (Prepend "a" (Empty {String}))))\n')
            path.write_text(dependent)
            checked = project('run')
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertEqual(checked.stdout, 'a\n')
            path.write_text(source)
            # Shape recognition is deliberately narrow; reject negative,
            # nonuniform, nonlinear, dependent and multi-field recursion.
            bad = [authored.replace('{0 A : Type}', '{A : Type}'),
                   authored.replace('(1 head : A)', '(head : A)'),
                   authored.replace('(1 tail : Items A)', '(tail : Items A)'),
                   authored.replace('(1 tail : Items A)', '(0 tail : Items A)'),
                   authored.replace('(1 tail : Items A)', '(1 tail : Items Bool)'),
                   authored.replace('(1 tail : Items A)', '(1 tail : Items A -> String)'),
                   authored.replace('(1 tail : Items A)', '(1 tail : Items A) -> (1 extra : A)'),
                   authored.replace('Empty : Items A', 'Empty : Items String'),
                   authored.replace('  Empty : Items A\n', '')]
            for program in bad:
                with self.subTest(program=program):
                    library.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertEqual(rejected.stdout, '')
            library.write_text(authored)
            direct = ('module Main\nimport Data.Items\nmain : IO Unit\nmain = putStrLn '
                      '(case Data.Items.Empty {String} of\n'
                      '  Data.Items.Empty => "empty"\n'
                      '  Data.Items.Prepend item => item)\n')
            path.write_text(direct)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # A repeated fold step cannot discard its linear head.
            dropped = source.replace('appendString item result', 'result')
            path.write_text(dropped)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            helper = ('consume : (1 xs : Data.Items.Items String) -> String\n'
                      'consume xs = Data.Items.foldItems String (\\(0 self : Data.Items.Items String) => String) "" '
                      '(\\(1 head : String) => \\(0 tail : Data.Items.Items String) => '
                      '\\(1 result : String) => appendString head result) xs\n\n')
            bad_tail = source.replace('appendString item result', 'appendString item (appendString (consume rest) result)').replace(
                'join : (1 items', helper + 'join : (1 items')
            path.write_text(bad_tail)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Binder usage: expected 0, observed 1', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            capture = source.replace('join : (1 items', 'join : (1 prefix : String) -> (1 items').replace(
                'join items =', 'join prefix items =').replace('appendString item result',
                'appendString prefix (appendString item result)').replace('(join (Data.Items.Prepend', '(join "p" (Data.Items.Prepend')
            path.write_text(capture)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Binder usage: expected 1, observed unrestricted', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            path.write_text(source.replace('Data.Items.Empty {String}', 'Data.Items.Empty {Bool}'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')

    def test_user_defined_unary_recursive_data(self):
        import shutil
        fixture = ROOT / 'examples/modules/recursive-data'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture, root, dirs_exist_ok=True)
            path = root / 'Main.fib'
            library = root / 'Data/Chain.fib'
            source, authored = path.read_text(), library.read_text()
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '!!\n')
            lines = source.splitlines()
            row = next(i for i, line in enumerate(lines, 1) if 'Data.Chain.More' in line)
            col = lines[row - 1].index('Data.Chain.More') + len('Data.Chain.') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(row), str(col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(Path(json.loads(nav.stdout)['definition']['path']).name, 'Chain.fib')
            path.write_text(source.replace('Data.Chain.', ''))
            self.assertEqual(project('run').stdout, '!!\n')
            path.write_text(source)
            ir = run('elaborate', str(library))
            self.assertEqual(ir.returncode, 0, ir.stderr)
            self.assertIn('recursive-type', ir.stdout)
            self.assertIn('recursive-fold', ir.stdout)
            for file in [path, library]:
                formatted = run('format', str(file))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                file.write_text(formatted.stdout)
                self.assertEqual(run('format', '--check', str(file)).returncode, 0)
            self.assertEqual(project('run').stdout, '!!\n')
            # Declaration order and fully qualified direct self references
            # produce the same checked recursive family.
            reversed_order = authored.replace('  Empty : Chain\n  More : (1 rest : Chain) -> Chain',
                                               '  More : (1 rest : Chain) -> Chain\n  Empty : Chain')
            library.write_text(reversed_order)
            self.assertEqual(project('run').stdout, '!!\n')
            qualified = authored.replace('(1 rest : Chain)', '(1 rest : Data.Chain.Chain)')
            library.write_text(qualified)
            self.assertEqual(project('run').stdout, '!!\n')
            library.write_text(authored.replace('export\ndata Chain', 'data Chain'))
            private = project('run')
            self.assertNotEqual(private.returncode, 0)
            self.assertEqual(private.stdout, '')
            library.write_text(authored.replace('  eliminator foldChain\n', ''))
            missing = project('run')
            self.assertNotEqual(missing.returncode, 0)
            self.assertEqual(missing.stdout, '')
            path.write_text('module Main\nimport Data.Chain\nmain : IO Unit\nmain = putStrLn "no helper"\n')
            self.assertEqual(project('run').stdout, 'no helper\n')
            path.write_text(source)
            library.write_text(authored)
            dependency, client = root / 'dependency', root / 'client'
            (dependency / 'src/Data').mkdir(parents=True)
            (dependency / 'src/Data/Chain.fib').write_text(authored)
            (dependency / 'fibril.yaml').write_text('schema: 1\nname: chain-lib\nmodule-prefix: Data.Chain\nsource-dir: src\nfoundation: de-morgan\nmodules: [Data.Chain]\ndependencies: {}\n')
            (client / 'src').mkdir(parents=True)
            (client / 'src/Main.fib').write_text(source)
            (client / 'fibril.yaml').write_text('schema: 1\nname: chain-client\nmodule-prefix: Demo\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  chain-lib:\n    path: ../dependency\n')
            packaged = run('run', '--package', str(client / 'fibril.yaml'))
            self.assertEqual(packaged.returncode, 0, packaged.stdout + packaged.stderr)
            self.assertEqual(packaged.stdout, '!!\n')
            # The generated fold checks a motive dependent on the *actual*
            # recursive value, even with a neutral predecessor.
            dependent = ('module Main\ndata Chain : Type where\n  eliminator foldChain\n'
                         '  Empty : Chain\n  More : (1 rest : Chain) -> Chain\n'
                         'data Tagged (0 chain : Chain) : Type where\n  Bad : Tagged chain\n'
                         '  Mark : (1 text : String) -> Tagged chain\n'
                         'build : (1 chain : Chain) -> Tagged chain\n'
                         'build chain = foldChain (\\(0 self : Chain) => Tagged self) (Mark Empty "z") '
                         '(\\(0 rest : Chain) => \\(1 previous : Tagged rest) => case previous of\n'
                         '  Bad => Bad (More rest)\n  Mark text => Mark (More rest) (appendString text "!")) chain\n'
                         'show : (0 chain : Chain) -> (1 value : Tagged chain) -> String\n'
                         'show chain value = case value of\n  Bad => "bad"\n  Mark text => text\n'
                         'main : IO Unit\nmain = putStrLn (show (More Empty) (build (More Empty)))\n')
            path.write_text(dependent)
            checked = project('run')
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            self.assertEqual(checked.stdout, 'z!\n')
            # Unsupported recursive shapes are rejected, not interpreted as
            # positive by an unchecked name or descriptor.
            bad = [authored.replace('(1 rest : Chain)', '(rest : Chain)'),
                   authored.replace('(1 rest : Chain)', '(0 rest : Chain)'),
                   authored.replace('(1 rest : Chain)', '(1 rest : Chain -> String)'),
                   authored.replace('(1 rest : Chain)', '(1 rest : Chain) -> (1 extra : Chain)'),
                   authored.replace('  Empty : Chain\n', ''),
                   authored.replace('data Chain : Type', 'data Chain (0 A : Type) : Type'),
                   authored.replace('More : (1 rest : Chain) -> Chain', 'More : (1 rest : Chain) -> String')]
            path.write_text(source)
            for program in bad:
                with self.subTest(program=program):
                    library.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertEqual(rejected.stdout, '')
            library.write_text(authored)
            different = ('module Main\ndata A : Type where\n  AEnd : A\n  AMore : (1 tail : A) -> A\n'
                         'data B : Type where\n  BEnd : B\n  BMore : (1 tail : B) -> B\n'
                         'bad : A\nbad = BMore BEnd\nmain : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(different)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # The structural helper does not expose its erased predecessor at
            # runtime or allow the repeated step to capture a linear value.
            stage = ('module Main\ndata Chain : Type where\n  eliminator foldChain\n  Empty : Chain\n'
                     '  More : (1 rest : Chain) -> Chain\n'
                     'bad : (1 chain : Chain) -> Chain\nbad chain = foldChain '
                     '(\\(0 self : Chain) => Chain) Empty '
                     '(\\(0 rest : Chain) => \\(1 result : Chain) => rest) chain\n'
                     'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(stage)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            capture = ('module Main\ndata Chain : Type where\n  eliminator foldChain\n  Empty : Chain\n'
                       '  More : (1 rest : Chain) -> Chain\n'
                       'bad : (1 prefix : String) -> (1 chain : Chain) -> String\n'
                       'bad prefix chain = foldChain (\\(0 self : Chain) => String) "" '
                       '(\\(0 rest : Chain) => \\(1 result : String) => appendString prefix result) chain\n'
                       'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(capture)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')

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
            # A recursive constructor with no base case is a legal general family (it has no
            # values), no longer a refusal: recursion is checked by positivity, not forbidden.
            path.write_text(base.replace('MkFlag : Flag A', 'MkFlag : (1 child : Flag A) -> Flag A'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual((result.returncode, result.stdout), (0, "flags\n"), result.stderr)
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
                                    ("import Text", 7)):
                    expect(query(entry, sources[entry], token, skip), library, "Text.Greeting")
                self.assertIsNone(query(entry, sources[entry], '"local"', 1))
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

    def test_shared_module_reference_chain_does_not_expand(self):
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
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Module checking: accepted", result.stdout)

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

    def test_explicitly_declared_implicit_arguments(self):
        import shutil
        fixture = ROOT / 'examples/modules/implicit-arguments'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture, root, dirs_exist_ok=True)
            path = root / 'Main.fib'
            library = root / 'Utility/Identity.fib'
            original = path.read_text()
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'queued: receipt\nexplicit type\nphantom type\nboth inferred\npartly explicit\n')
            # Visibility metadata also crosses an explicit package edge.
            dependency = root / 'dependency'
            client = root / 'client'
            (dependency / 'src/Utility').mkdir(parents=True)
            (dependency / 'src/Utility/Identity.fib').write_text(library.read_text())
            (dependency / 'fibril.yaml').write_text('schema: 1\nname: implicit-lib\nmodule-prefix: Utility.Identity\nsource-dir: src\nfoundation: de-morgan\nmodules: [Utility.Identity]\ndependencies: {}\n')
            (client / 'src').mkdir(parents=True)
            (client / 'src/Main.fib').write_text(original)
            (client / 'fibril.yaml').write_text('schema: 1\nname: implicit-client\nmodule-prefix: Demo\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  implicit-lib:\n    path: ../dependency\n')
            package_result = run('run', '--package', str(client / 'fibril.yaml'))
            self.assertEqual(package_result.returncode, 0, package_result.stdout + package_result.stderr)
            self.assertEqual(package_result.stdout, result.stdout)
            library_source = library.read_text()
            library.write_text(library_source.replace('export\nkeep', 'keep', 1))
            private = project('run')
            self.assertNotEqual(private.returncode, 0)
            self.assertEqual(private.stdout, '')
            library.write_text(library_source)
            definition = json.loads(run('definition', '4', '35', str(library)).stdout)['definition']
            self.assertEqual((definition['start']['line'], definition['start']['column']), (4, 11))
            # Rename remains same-file only; a module header cannot be renamed
            # until project-aware rename exists. Test authored binder sites on
            # an equivalent unsaved-style standalone source snapshot.
            rename_file = root / 'rename.fib'
            rename_file.write_text('identity : {0 A : Type} -> (1 value : A) -> A\nidentity T item = item\nmain : IO Unit\nmain = putStrLn "ok"\n')
            rename = run('rename-preview', '1', '15', 'Element', str(rename_file))
            self.assertEqual(rename.returncode, 0, rename.stderr)
            self.assertEqual(len(json.loads(rename.stdout)['edits']), 3)
            for file in [path, library]:
                formatted = run('format', str(file))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                file.write_text(formatted.stdout)
                self.assertEqual(run('format', '--check', str(file)).returncode, 0)
            self.assertEqual(project('run').stdout, result.stdout)
            invalid = [
                original.replace('Utility.Identity.label {Bool}', 'Utility.Identity.label'),
                original.replace('Utility.Identity.keep {String}', 'Utility.Identity.keep {Bool}'),
                original.replace('Utility.Identity.keep {String}', 'Utility.Identity.keep String'),
                original.replace('Utility.Identity.keep {String}', 'Utility.Identity.keep {}'),
                original.replace('Utility.Identity.keep {String}', 'Utility.Identity.keep {String'),
            ]
            for program in invalid:
                with self.subTest(program=program[-100:]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            path.write_text(original.replace('Utility.Identity.label {Bool}', 'Utility.Identity.label'))
            self.assertIn('ambiguous', project('run').stderr)
            # Local shadowing and ordinary erased positional parameters are unchanged.
            shadow = ('module Main\nkeep : {0 A : Type} -> (1 value : A) -> A\nkeep T item = item\n'
                      'local : (1 keep : (1 text : String) -> String) -> String\nlocal keep = keep "shadow"\n'
                      'old : (0 A : Type) -> (1 value : A) -> A\nold T value = value\n'
                      'main : IO Unit\nmain = putStrLn (old String (local (\\(1 text : String) => text)))\n')
            path.write_text(shadow)
            shadowed = project('run')
            self.assertEqual(shadowed.returncode, 0, shadowed.stdout + shadowed.stderr)
            self.assertEqual(shadowed.stdout, 'shadow\n')
            path.write_text(shadow.replace('old String (local', 'old {String} (local'))
            self.assertNotEqual(project('run').returncode, 0)
            # Implicit solutions can refer to an outer erased type variable.
            generic = ('module Main\nidentity : {0 A : Type} -> (1 value : A) -> A\nidentity T value = value\n'
                       'outer : (0 A : Type) -> (1 value : A) -> A\nouter T value = identity value\n'
                       'main : IO Unit\nmain = putStrLn (outer String "scoped")\n')
            path.write_text(generic)
            self.assertEqual(project('run').stdout, 'scoped\n')
            nominal = ('module Main\ndata Option (0 A : Type) : Type where\n  None : Option A\n  Some : (1 value : A) -> Option A\n'
                       'same : {0 A : Type} -> (1 value : Option A) -> Option A\nsame T value = value\n'
                       'show : (1 value : Option String) -> String\nshow value = case value of\n  None => "none"\n  Some text => text\n'
                       'main : IO Unit\nmain = putStrLn (show (same (Some String "nominal")))\n')
            path.write_text(nominal)
            nominal_result = project('run')
            self.assertEqual(nominal_result.returncode, 0, nominal_result.stdout + nominal_result.stderr)
            self.assertEqual(nominal_result.stdout, 'nominal\n')
            for signature in ['{A : Type} -> (1 x : A) -> A',
                              '{1 A : Type} -> (1 x : A) -> A',
                              '(1 x : String) -> {0 A : Type} -> String']:
                path.write_text('module Main\nbad : ' + signature + '\nbad = "no"\nmain : IO Unit\nmain = putStrLn "never"\n')
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            # Conflicting and escaping solutions are never silently guessed.
            cases = [
                ('same : {0 A : Type} -> (1 f : (1 x : A) -> A) -> (1 x : A) -> A\nsame T f = f\n',
                 'same (\\(1 x : String) => True) "x"'),
                ('wrap : {0 A : Type} -> (1 f : (0 T : Type) -> (1 x : A) -> A) -> (0 T : Type) -> (1 x : A) -> A\nwrap A f = f\n',
                 'wrap (\\(0 T : Type) => \\(1 x : T) => x) String "x"'),
            ]
            for declaration, call in cases:
                path.write_text('module Main\n' + declaration + 'main : IO Unit\nmain = putStrLn (' + call + ')\n')
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertEqual(rejected.stdout, '')
                self.assertIn('explicit {argument', rejected.stderr)
            # Existing quantitative checks remain authoritative after insertion.
            bad_usage = [
                'leak : {0 A : Type} -> (0 value : A) -> A\nleak T value = value\n',
                'duplicate : {0 A : Type} -> (1 text : String) -> String\nduplicate T text = appendString text text\n',
                '0 secret : String\nsecret = "hidden"\nidentity : {0 A : Type} -> (1 value : A) -> A\nidentity T value = value\nmain : IO Unit\nmain = putStrLn (identity secret)\n',
            ]
            for program in bad_usage:
                if 'main : IO Unit' not in program:
                    program += 'main : IO Unit\nmain = putStrLn "never"\n'
                path.write_text('module Main\n' + program)
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            # Function types over the inference admission still have the
            # explicit-brace fallback; no result is guessed after exhaustion.
            chain = ' -> '.join(['String'] * 131)
            huge = f'({chain}) -> ({chain})'
            oversized = ('module Main\n' +
                         f'id : {{0 A : Type}} -> (1 x : ({huge})) -> ({huge})\n' +
                         f'id = \\(0 T : Type) => \\(1 x : ({huge})) => x\n' +
                         f'use : (1 x : ({huge})) -> ({huge})\n' +
                         f'use = \\(1 x : ({huge})) => id {{Bool}} x\n' +
                         'main : IO Unit\nmain = putStrLn "ok"\n')
            path.write_text(oversized)
            self.assertEqual(project('run').stdout, 'ok\n')
            path.write_text(oversized.replace('id {Bool} x', 'id x'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Implicit function type exceeds 512 nodes', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # A new signature cannot silently become implicit in standalone files.
            plain = root / 'plain.fib'
            plain.write_text('identity : {0 A : Type} -> (1 value : A) -> A\nidentity T x = x\nmain : IO Unit\nmain = putStrLn (identity "x")\n')
            self.assertNotEqual(run('run', str(plain)).returncode, 0)

    def test_structural_nat_recursive_string_equations(self):
        source = (ROOT / 'examples/modules/recursive-render/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'receipt!!\n')
            nominal = ('module Main\ndata Result : Type where\n  Bad : Result\n  Good : (1 message : String) -> Result\n'
                       'identity : {0 A : Type} -> (1 value : A) -> A\nidentity A value = value\n'
                       'build : (1 count : Nat) -> Result\nbuild count = case count of\n'
                       '  Zero => Good "ok"\n  Succ smaller => identity (build smaller)\n'
                       'show : (1 result : Result) -> String\nshow result = case result of\n'
                       '  Bad => "bad"\n  Good message => message\n'
                       'main : IO Unit\nmain = putStrLn (show (build (Succ (Succ Zero))))\n')
            path.write_text(nominal)
            nominal_result = project('run')
            self.assertEqual(nominal_result.returncode, 0, nominal_result.stdout + nominal_result.stderr)
            self.assertEqual(nominal_result.stdout, 'ok\n')
            # Result annotations and referenced globals are reserved before
            # the transformed branch is elaborated and copied.
            def wide_result(width):
                ty = ' -> '.join(['String'] * (width + 1))
                value = ''.join(f'\\(x{i} : String) => ' for i in range(width)) + '"end"'
                return (f'module Main\n0 Result : Type\nResult = {ty}\nbase : Result\nbase = {value}\n'
                        'f : (1 n : Nat) -> Result\nf n = case n of\n'
                        '  Zero => base\n  Succ k => f k\nmain : IO Unit\nmain = putStrLn "ok"\n')
            path.write_text(wide_result(60))
            wide = project('run')
            self.assertEqual(wide.returncode, 0, wide.stdout + wide.stderr)
            self.assertEqual(wide.stdout, 'ok\n')
            path.write_text(wide_result(130))
            wider = project('run')
            # Past the structural lowering's width limit the general path still applies.
            self.assertEqual(wider.returncode, 0, wider.stdout + wider.stderr)
            self.assertEqual(wider.stdout, 'ok\n')
            self.assertNotIn('Internal module expansion estimate was insufficient', wider.stderr)
            with_global = source.replace('render : (1 count : Nat)', 'suffix : String\nsuffix = "?"\nrender : (1 count : Nat)').replace('appendString (render smaller) "!"', 'appendString (render smaller) suffix')
            path.write_text(with_global)
            self.assertEqual(project('run').stdout, 'receipt??\n')
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(project('run').stdout, 'receipt??\n')
            zero = source.replace('Succ (Succ Zero)', 'Zero')
            path.write_text(zero)
            self.assertEqual(project('run').stdout, 'receipt\n')
            path.write_text(source)
            line = next(i for i, row in enumerate(source.splitlines(), 1) if 'render smaller' in row)
            col = source.splitlines()[line - 1].index('render smaller') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(line), str(col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(json.loads(nav.stdout)['definition']['range']['start']['line'], 5)
            # No hidden, repeated or non-decreasing recursive use is accepted.
            bad = ['appendString (render count) "!"',
                   'appendString (render (Succ smaller)) "!"',
                   'appendString (render smaller) (render smaller)',
                   'appendString (render smaller) (render Zero)',
                   'if True then render smaller else "unused"',
                   'appendString (render smaller) (render : Nat -> String)',
                   '(\\(1 x : String) => x) (render smaller)']
            for body in bad:
                with self.subTest(body=body):
                    path.write_text(source.replace('appendString (render smaller) "!"', body))
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertEqual(rejected.stdout, '')
            path.write_text(source.replace('Zero => "receipt"', 'Zero => render Zero'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Even syntactically admitted branches undergo the normal type
            # checker; a Nat is not a String result.
            path.write_text(source.replace('appendString (render smaller) "!"', 'Succ (render smaller)'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')

    def test_structural_nat_recursive_equations(self):
        source = (ROOT / 'examples/modules/recursive-equations/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '!!!!\n')
            self_line = next(i for i, line in enumerate(source.splitlines(), 1) if 'double smaller' in line)
            self_col = source.splitlines()[self_line - 1].index('double smaller') + 1
            nav = run('definition', '--source-dir', directory, '--entry', str(path), str(self_line), str(self_col), str(path))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(json.loads(nav.stdout)['definition']['range']['start']['line'], 5)
            # Checked function type aliases are admitted by guarded conversion.
            alias = source.replace('double : (1 count : Nat) -> Nat', '0 NatFunction : Type\nNatFunction = (1 count : Nat) -> Nat\ndouble : NatFunction')
            path.write_text(alias)
            alias_result = project('run')
            self.assertEqual(alias_result.returncode, 0, alias_result.stdout + alias_result.stderr)
            self.assertEqual(alias_result.stdout, '!!!!\n')
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(project('run').stdout, '!!!!\n')
            reversed_arms = source.replace('  Zero => Zero\n  Succ smaller => Succ (Succ (double smaller))',
                                           '  Succ smaller => Succ (Succ (double smaller))\n  Zero => Zero')
            path.write_text(reversed_arms)
            self.assertEqual(project('run').stdout, '!!!!\n')
            # None of these calls is the unique admitted recursive call on the
            # immediate predecessor; no failed match becomes a core fixpoint.
            bad_steps = ['double count', 'double (Succ smaller)',
                         'Succ (double (double smaller))',
                         'double', 'double {Nat} smaller']
            for step in bad_steps:
                with self.subTest(step=step):
                    path.write_text(source.replace('Succ (Succ (double smaller))', step))
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertEqual(rejected.stdout, '')
            # A let that copies the predecessor and recurses on the copy still terminates, so general
            # recursion accepts it (it computes something else: double is always zero here).
            path.write_text(source.replace('Succ (Succ (double smaller))', '(\\(1 smaller : Nat) => double smaller) smaller'))
            copied = project('run')
            self.assertEqual(copied.returncode, 0, copied.stdout + copied.stderr)
            self.assertEqual(copied.stdout, '\n')
            for changed in [source.replace('Succ smaller =>', 'Succ double =>'),
                            source.replace('double count = case count', 'double Zero = case Zero'),
                            source.replace('Zero => Zero', 'Zero => double Zero')]:
                path.write_text(changed)
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            # An unrestricted count is outside the linear structural form, but its predecessor is
            # then unrestricted too, so the general recursion path accepts it.
            path.write_text(source.replace('(1 count : Nat)', '(count : Nat)', 1))
            unrestricted = project('run')
            self.assertEqual(unrestricted.returncode, 0, unrestricted.stdout + unrestricted.stderr)
            self.assertEqual(unrestricted.stdout, '!!!!\n')
            # A visible imported name—even an identical alias—must not be
            # silently reinterpreted as a built-in constructor pattern.
            (root / 'Other.fib').write_text('module Other\nexport\nZero : Nat\nZero = Zero\n')
            path.write_text(source.replace('module Main\n', 'module Main\nimport Other\n'))
            aliased = project('run')
            # No structural recognizer reinterprets the alias; the general path resolves
            # the Zero pattern exactly as it does for non-recursive code, so this runs.
            self.assertEqual(aliased.returncode, 0, aliased.stdout + aliased.stderr)
            # Ambiguous imported names are not silently turned into a self-call.
            for module in ['A', 'B']:
                (root / f'{module}.fib').write_text(f'module {module}\nexport\ndouble : (1 n : Nat) -> Nat\ndouble n = n\n')
            path.write_text(source.replace('module Main\n', 'module Main\nimport A\nimport B\n'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # An unchecked duplicating type expression must fail within
            # conversion admission, rather than being expanded unchecked.
            huge = 'Nat'
            for _ in range(14):
                huge = '(\\(0 T : Type) => T -> T) (' + huge + ')'
            path.write_text(source.replace('(1 count : Nat) -> Nat', huge, 1))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Standalone declarations do not publish this module-only lowering.
            plain = root / 'plain.fib'
            plain.write_text(source.replace('module Main\n', ''))
            self.assertNotEqual(run('run', str(plain)).returncode, 0)

    def test_runtime_nat_predecessor(self):
        source = (ROOT / 'examples/modules/nat-predecessor/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '!!!\n')
            path.write_text(source.replace('triangle : (count : Nat)', 'triangle : (1 count : Nat)'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Binder usage: expected 1, observed unrestricted', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # An erased predecessor cannot stand in for the unrestricted
            # predecessor required by this distinct recursor.
            path.write_text(source.replace('(\\(k : Nat) => \\(1 result : Nat)', '(\\(0 k : Nat) => \\(1 result : Nat)'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')

    def test_total_nat_recursion(self):
        source = (ROOT / 'examples/modules/nat-recursion/Main.fib').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'receipt!!!\n')
            zero = source.replace('Succ (Succ (Succ Zero))', 'Zero')
            path.write_text(zero)
            self.assertEqual(project('run').stdout, 'receipt\n')
            # Recursion is through natRec only; a source self-call has no
            # independently checked decreasing-argument certificate.
            path.write_text('module Main\nloop : (1 n : Nat) -> String\nloop n = loop n\nmain : IO Unit\nmain = putStrLn (loop Zero)\n')
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Erased predecessors cannot be returned at runtime, even when
            # the current scrutinee is a known successor.
            invalid = ('module Main\nbad : (1 n : Nat) -> Nat\n'
                       'bad n = natRec (\\(0 k : Nat) => Nat) Zero '
                       '(\\(0 k : Nat) => \\(1 result : Nat) => k) n\n'
                       'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(invalid)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Inference can use direct Nat values and a recursor result.
            generic = ('module Main\nidentity : {0 A : Type} -> (1 x : A) -> A\nidentity A x = x\n'
                       'use : (1 n : Nat) -> String\nuse n = natRec (\\(0 k : Nat) => String) "z" '
                       '(\\(0 k : Nat) => \\(1 x : String) => appendString x "!") n\n'
                       'main : IO Unit\nmain = putStrLn (use (identity (Succ (identity Zero))))\n')
            path.write_text(generic)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'z!\n')
            indexed = ('module Main\ndata Mark (0 n : Nat) : Type where\n'
                       '  A : (1 value : String) -> Mark n\n  B : (1 value : String) -> Mark n\n'
                       'read : {0 n : Nat} -> (1 value : Mark (Succ n)) -> String\n'
                       'read n value = case value of\n  A text => text\n  B text => text\n'
                       'main : IO Unit\nmain = putStrLn (read (A (Succ Zero) "index"))\n')
            path.write_text(indexed)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'index\n')
            dependent = ('module Main\ndata Mark (0 n : Nat) : Type where\n'
                         '  A : (1 value : String) -> Mark n\n  B : (1 value : String) -> Mark n\n'
                         'carry : (1 n : Nat) -> Mark n\n'
                         'carry n = natRec (\\(0 k : Nat) => Mark k) (A Zero "z") '
                         '(\\(0 k : Nat) => \\(1 prev : Mark k) => case prev of\n'
                         '  A text => A (Succ k) (appendString text "!")\n'
                         '  B text => B (Succ k) (appendString text "!")) n\n'
                         'show : (0 n : Nat) -> (1 value : Mark n) -> String\n'
                         'show n value = case value of\n  A text => text\n  B text => text\n'
                         'main : IO Unit\nmain = putStrLn (show (Succ Zero) (carry (Succ Zero)))\n')
            path.write_text(dependent)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'z!\n')
            # The runtime-predecessor recursor also handles the dependent
            # motive; only its count and step predecessor become unrestricted.
            with_runtime_pred = (dependent.replace('carry : (1 n : Nat)', 'carry : (n : Nat)')
                                 .replace('carry n = natRec ', 'carry n = natRecWith ')
                                 .replace('(\\(0 k : Nat) => \\(1 prev : Mark k)', '(\\(k : Nat) => \\(1 prev : Mark k)'))
            path.write_text(with_runtime_pred)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'z!\n')

    def test_implicit_data_constructors(self):
        import shutil
        fixture = ROOT / 'examples/modules/implicit-constructors'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixture, root, dirs_exist_ok=True)
            path = root / 'Main.fib'
            library = root / 'Data/Choice.fib'
            source = path.read_text()
            authored = library.read_text()
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'receipt\n')
            # Brace-only nullary application and partial braces are explicit;
            # expected results solve phantom constructor parameters.
            path.write_text(source.replace('Data.Choice.Left "receipt"', 'Data.Choice.Left {String} "receipt"'))
            self.assertEqual(project('run').stdout, 'receipt\n')
            path.write_text(source.replace('Data.Choice.Left "receipt"', 'Data.Choice.Left {String} {Bool} "receipt"'))
            self.assertEqual(project('run').stdout, 'receipt\n')
            path.write_text(source.replace('Data.Choice.Left "receipt"', 'Data.Choice.Right True'))
            self.assertEqual(project('run').stdout, 'accepted\n')
            path.write_text(source.replace('Data.Choice.None {String}', 'Data.Choice.Some "item"'))
            self.assertEqual(project('run').stdout, 'receipt\n')
            # Both nullary and unary direct cases inspect checked constructors.
            option_case = ('render : (1 choice : Data.Choice.Option String) -> String\n'
                           'render choice = case choice of\n'
                           '  Data.Choice.None => "none"\n'
                           '  Data.Choice.Some text => text\n'
                           'main : IO Unit\nmain = putStrLn (render explicit)\n')
            path.write_text(source[:source.index('main : IO Unit')] + option_case)
            self.assertEqual(project('run').stdout, 'none\n')
            path.write_text((source[:source.index('main : IO Unit')] + option_case).replace('Data.Choice.None {String}', 'Data.Choice.Some "item"'))
            self.assertEqual(project('run').stdout, 'item\n')
            # Generated eliminator applications use explicit constructor braces
            # internally while the public eliminator parameters remain ordinary.
            folded = ('folded : (1 choice : Data.Choice.Choice String Bool) -> String\n'
                      'folded choice = Data.Choice.useChoice String Bool '
                      '(\\(0 self : Data.Choice.Choice String Bool) => String) choice '
                      '(\\(1 text : String) => text) '
                      '(\\(1 flag : Bool) => if flag then "yes" else "no")\n'
                      'main : IO Unit\nmain = putStrLn (folded sample)\n')
            path.write_text(source[:source.index('main : IO Unit')] + folded)
            self.assertEqual(project('run').stdout, 'receipt\n')
            # Dependent implicit domains may refer to earlier parameters;
            # the nominal expected result supplies the erased index.
            dependent = ('module Main\ndata Tagged {0 A : Type} {0 label : A} : Type where\n'
                         '  TaggedValue : (1 value : A) -> Tagged A label\n'
                         'item : Tagged String "subject"\nitem = TaggedValue "receipt"\n'
                         'main : IO Unit\nmain = putStrLn "ok"\n')
            path.write_text(dependent)
            dep = project('run')
            self.assertEqual(dep.returncode, 0, dep.stdout + dep.stderr)
            self.assertEqual(dep.stdout, 'ok\n')
            # An erased value may not be smuggled into a runtime field.
            path.write_text(source.replace('sample : Data.Choice.Choice String Bool',
                                           '0 secret : String\nsecret = "hidden"\nsample : Data.Choice.Choice String Bool').replace('Data.Choice.Left "receipt"', 'Data.Choice.Left secret'))
            stage = project('run')
            self.assertNotEqual(stage.returncode, 0)
            self.assertEqual(stage.stdout, '')
            # Bare nullary constructors are not silently instantiated.
            path.write_text(source.replace('Data.Choice.None {String}', 'Data.Choice.None'))
            bare = project('run')
            self.assertNotEqual(bare.returncode, 0)
            self.assertEqual(bare.stdout, '')
            # Wrong explicit solutions and old positional spelling fail for
            # the opt-in declaration, before any console effect.
            for bad in ['Data.Choice.Left {Bool} {Bool} "receipt"',
                        'Data.Choice.Left String Bool "receipt"',
                        'Data.Choice.Left {String} {Bool} {Bool} "receipt"']:
                path.write_text(source.replace('Data.Choice.Left "receipt"', bad))
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertEqual(rejected.stdout, '')
            # Missing phantom information remains ambiguous without an
            # expected constructor result; no guessed solution reaches core.
            ambiguous = ('identity : {0 T : Type} -> (1 x : T) -> T\nidentity T x = x\n' +
                         'main : IO Unit\nmain = putStrLn (showChoice (identity (Data.Choice.Left "x")))\n')
            path.write_text(source[:source.index('main : IO Unit')] + ambiguous)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('ambiguous', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # Header syntax is opt-in, uniform, quantity-zero and preserved by
            # formatter shape checking; generated eliminators also check.
            path.write_text(source)
            for file in [path, library]:
                formatted = run('format', str(file))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                file.write_text(formatted.stdout)
                self.assertEqual(run('format', '--check', str(file)).returncode, 0)
            self.assertEqual(project('run').stdout, 'receipt\n')
            for invalid in [authored.replace('{0 A : Type}', '{A : Type}', 1),
                            authored.replace('{0 A : Type}', '{1 A : Type}', 1),
                            authored.replace('{0 B : Type}', '(0 B : Type)', 1),
                            authored.replace('{0 A : Type}', '(0 A : Type)', 1)]:
                library.write_text(invalid)
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            library.write_text(authored.replace('export\ndata Choice', 'data Choice', 1))
            private = project('run')
            self.assertNotEqual(private.returncode, 0)
            self.assertEqual(private.stdout, '')
            library.write_text(authored + '\nexport\nshadow : (1 Left : (1 text : String) -> String) -> String\nshadow Left = Left "local"\n')
            path.write_text(source.replace('showChoice sample', 'Data.Choice.shadow (\\(1 text : String) => text)'))
            shadowed = project('run')
            self.assertEqual(shadowed.returncode, 0, shadowed.stdout + shadowed.stderr)
            self.assertEqual(shadowed.stdout, 'local\n')
            path.write_text(source)
            library.write_text(authored)
            # Header names and type uses navigate to actual authored tokens.
            definition = json.loads(run('definition', '6', '21', str(library)).stdout)['definition']
            self.assertEqual((definition['start']['line'], definition['start']['column']), (4, 16))
            # Checked metadata survives an explicit package edge.
            dependency, client = root / 'dependency', root / 'client'
            (dependency / 'src/Data').mkdir(parents=True)
            (dependency / 'src/Data/Choice.fib').write_text(authored)
            (dependency / 'fibril.yaml').write_text('schema: 1\nname: choice-lib\nmodule-prefix: Data.Choice\nsource-dir: src\nfoundation: de-morgan\nmodules: [Data.Choice]\ndependencies: {}\n')
            (client / 'src').mkdir(parents=True)
            (client / 'src/Main.fib').write_text(source)
            (client / 'fibril.yaml').write_text('schema: 1\nname: choice-client\nmodule-prefix: Demo\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  choice-lib:\n    path: ../dependency\n')
            packaged = run('run', '--package', str(client / 'fibril.yaml'))
            self.assertEqual(packaged.returncode, 0, packaged.stdout + packaged.stderr)
            self.assertEqual(packaged.stdout, 'receipt\n')

    def test_multiple_implicit_constraints_and_expected_results(self):
        fixture = ROOT / 'examples/modules/implicit-constraints/Main.fib'
        source = fixture.read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'receipt\n')
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'receipt\n')
            # Expected result from a later function argument solves phantom B.
            nested = source.replace('render sample)', 'render (inject "nested"))')
            path.write_text(nested)
            self.assertEqual(project('run').stdout, 'nested\n')
            partial = source.replace('sample : Sum String Bool\nsample = inject "receipt"',
                'partial : (0 B : Type) -> (1 value : String) -> Sum String B\npartial = inject {String}\n'
                'sample : Sum String Bool\nsample = partial Bool "receipt"')
            path.write_text(partial)
            partial_result = project('run')
            self.assertEqual(partial_result.returncode, 0, partial_result.stdout + partial_result.stderr)
            self.assertEqual(partial_result.stdout, 'receipt\n')
            # An actually unconstrained implicit stays ambiguous, despite an
            # expected String result and a solved neighboring parameter.
            phantom = ('module Main\nphantom : {0 A : Type} -> {0 B : Type} -> (1 x : A) -> A\n'
                       'phantom T U x = x\nmain : IO Unit\nmain = putStrLn (phantom "x")\n')
            path.write_text(phantom)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('ambiguous', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            path.write_text(phantom.replace('phantom "x"', 'phantom {String} {Bool} "x"'))
            self.assertEqual(project('run').stdout, 'x\n')
            # Once the first two explicit arguments solve the prefix, the third
            # argument receives its expected type for its own implicit call.
            staged = ('module Main\ndata Choice (0 A : Type) (0 B : Type) : Type where\n'
                      '  L : (0 value : A) -> Choice A B\n  R : (0 value : B) -> Choice A B\n'
                      'inject : {0 A : Type} -> {0 B : Type} -> (0 value : A) -> Choice A B\n'
                      'inject T U value = L T U value\n'
                      'outer : {0 A : Type} -> {0 B : Type} -> (1 first : A) -> (second : B) -> (1 item : Choice String Bool) -> A\n'
                      'outer T U first second item = case item of\n  L x => first\n  R y => first\n'
                      'main : IO Unit\nmain = putStrLn (outer "kept" True (inject "receipt"))\n')
            path.write_text(staged)
            staged_result = project('run')
            self.assertEqual(staged_result.returncode, 0, staged_result.stdout + staged_result.stderr)
            self.assertEqual(staged_result.stdout, 'kept\n')
            fourth = staged.replace('(1 first : A) -> (second : B) -> (1 item', '(fixed : String) -> (1 first : A) -> (second : B) -> (1 item').replace('outer T U first second item =', 'outer T U fixed first second item =').replace('outer "kept" True (inject', 'outer "fixed" "kept" True (inject')
            path.write_text(fourth)
            fourth_result = project('run')
            self.assertEqual(fourth_result.returncode, 0, fourth_result.stdout + fourth_result.stderr)
            self.assertEqual(fourth_result.stdout, 'kept\n')
            # A supported Pi-type proposal retains prior single-prefix behavior.
            pi_type = ('module Main\nlabel : {0 A : Type 1} -> (0 x : A) -> String\n'
                       'label T x = "pi ok"\nmain : IO Unit\nmain = putStrLn (label ((1 x : String) -> String))\n')
            path.write_text(pi_type)
            self.assertEqual(project('run').stdout, 'pi ok\n')
            # An unavailable proposal is skipped; later constraints can solve.
            skipped = ('module Main\ndata Switch : Type where\n  Yes : Switch\n  No : Switch\n'
                       'f : {0 A : Type} -> {0 B : Type} -> (flag : Bool) -> (1 x : A) -> (z : B) -> A\n'
                       'f A B flag x z = x\nmain : IO Unit\nmain = putStrLn (f (case Yes of\n'
                       '  Yes => True\n  No => False) "ok" True)\n')
            path.write_text(skipped)
            skipped_result = project('run')
            self.assertEqual(skipped_result.returncode, 0, skipped_result.stdout + skipped_result.stderr)
            self.assertEqual(skipped_result.stdout, 'ok\n')
            # Implicit domains may depend on earlier inferred parameters;
            # the solver admits substitution before constructing the next type.
            dependent = ('module Main\ndata Tag (0 A : Type) (0 x : A) : Type where\n  Mk : Tag A x\n'
                         'use : {0 A : Type} -> {0 x : A} -> (1 token : Tag A x) -> String\n'
                         'use T value token = case token of\n  Mk => "ok"\n'
                         'consume : (1 token : Tag Bool True) -> String\nconsume token = use token\n'
                         'main : IO Unit\nmain = putStrLn (consume (Mk Bool True))\n')
            path.write_text(dependent)
            dependent_result = project('run')
            self.assertEqual(dependent_result.returncode, 0, dependent_result.stdout + dependent_result.stderr)
            self.assertEqual(dependent_result.stdout, 'ok\n')
            # Constraints on a later argument that require substituting an
            # earlier ordinary value are intentionally not guessed yet.
            rigid = ('module Main\nf : {0 A : Type} -> {0 B : Type} -> (0 T : Type) -> (x : T) -> (1 y : A) -> (z : B) -> A\n'
                     'f A B T x y z = y\nmain : IO Unit\nmain = putStrLn (f String "unused" "ok" True)\n')
            path.write_text(rigid)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            path.write_text(rigid.replace('f String "unused"', 'f {String} {Bool} String "unused"'))
            explicit = project('run')
            self.assertEqual(explicit.returncode, 0, explicit.stdout + explicit.stderr)
            self.assertEqual(explicit.stdout, 'ok\n')
            # Substitution is admitted before constructing an expanded
            # dependent telescope; explicit source arguments remain available.
            huge = ' -> '.join(['String'] * 131)
            expansion = ('module Main\nf : {0 A : Type} -> {0 B : Type} -> (1 x : A) -> (y : B) -> A\n'
                         'f A B x y = x\n' + f'use : (1 v : ({huge})) -> ({huge})\n' +
                         'use v = f v True\nmain : IO Unit\nmain = putStrLn "ok"\n')
            path.write_text(expansion)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Implicit telescope substitution exceeds', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            path.write_text(expansion.replace('f v True', f'f {{{huge}}} {{Bool}} v True'))
            explicit = project('run')
            self.assertEqual(explicit.returncode, 0, explicit.stdout + explicit.stderr)
            self.assertEqual(explicit.stdout, 'ok\n')
            # Constraint-work admission fails closed; explicit braces still work.
            big = 'x' * 600
            expensive = ('module Main\ndata Tag (0 x : String) (0 y : String) : Type where\n  Mk : Tag x y\n' +
                         f'use : {{0 y : String}} -> (1 t : Tag "{big}" y) -> String\n' +
                         'use y t = case t of\n  Mk => "ok"\n' +
                         f'caller : (1 t : Tag "{big}" "y") -> String\ncaller t = use t\n' +
                         f'main : IO Unit\nmain = putStrLn (caller (Mk "{big}" "y"))\n')
            path.write_text(expensive)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('constraint work admission exhausted', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            path.write_text(expensive.replace('caller t = use t', 'caller t = use {"y"} t'))
            self.assertEqual(project('run').stdout, 'ok\n')
            # Late and excess explicit braces fail rather than shifting slots.
            for bad in ['f String {Bool} "unused" "ok" True', 'f {String} {Bool} {String} String "unused" "ok" True']:
                path.write_text(rigid.replace('f String "unused" "ok" True', bad))
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            too_many = ''.join(f'{{0 A{i} : Type}} -> ' for i in range(65))
            path.write_text('module Main\nf : ' + too_many + '(1 x : String) -> String\nf = "bad"\nmain : IO Unit\nmain = putStrLn "never"\n')
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Implicit telescope admission exhausted', rejected.stderr)
            self.assertEqual(rejected.stdout, '')

    def test_named_function_equations_preserve_types_quantities_and_binders(self):
        example = ROOT / 'examples/modules/function-equations/Main.fib'
        original = example.read_text()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'Main.fib'
            path.write_text(original)
            def project(command):
                return run(command, '--source-dir', str(root), str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'status: \npreview: receipt\n')
            target = json.loads(run('definition', '8', '19', str(path)).stdout)['definition']
            self.assertEqual((target['start']['line'], target['start']['column']), (8, 12))
            references = json.loads(run('references', '8', '12', str(path)).stdout)['references']
            self.assertEqual([(x['start']['line'], x['start']['column']) for x in references], [(8, 12), (8, 19)])
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'status: \npreview: receipt\n')
            invalid = [
                original.replace('identity T item = item', 'identity T item = T'),
                original.replace('identity T item = item', 'identity T item = "wrong"'),
                original.replace('identity T item = item', 'identity T item item = item'),
                original.replace('identity T item = item', 'identity T item extra = item'),
                original.replace('identity T item = item', 'identity T (Left item) = item'),
                original.replace('identity T item = item', 'identity T item = identity T item'),
                original.replace('identity T item = item', 'identity T item = item\nidentity T item = item'),
                original.replace('describe prefix request =', 'describe prefix request = appendString prefix (appendString prefix "x")\ndescribe prefix request ='),
            ]
            for program in invalid:
                with self.subTest(program=program[:180]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            # Repeated use or discarding a linear equation parameter is rejected.
            for body in ['appendString text text', '"discarded"']:
                path.write_text('module Main\nbad : (1 text : String) -> String\nbad text = ' + body + '\nmain : IO Unit\nmain = putStrLn "never"\n')
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            path.write_text('module Main\nbad : (0 flag : Bool) -> Bool\nbad flag = flag\nmain : IO Unit\nmain = putStrLn "never"\n')
            self.assertNotEqual(project('run').returncode, 0)
            # Unchecked redex-headed signatures are not reduced during binder inference.
            path.write_text('module Main\nbad : (\\(0 A : Type) => A) ((1 x : String) -> String)\nbad x = x\nmain : IO Unit\nmain = putStrLn "never"\n')
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('requires an explicit Pi', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # Large explicit domains are rejected before copying into generated lambdas.
            side = ' '.join(['String'] * 140)
            path.write_text(f'module Main\nbad : (1 x : ({side}) ({side})) -> String\nbad x = "no"\nmain : IO Unit\nmain = putStrLn "never"\n')
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('parameter type exceeds 512 nodes', rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # Ordinary standalone declaration files and authored rename still work.
            standalone = root / 'plain.fib'
            standalone.write_text('identity : (0 A : Type) -> (1 item : A) -> A\nidentity T x = x\nmain : IO Unit\nmain = putStrLn (identity String "works")\n')
            self.assertEqual(run('run', str(standalone)).stdout, 'works\n')
            renamed = run('rename-preview', '2', '12', 'value', str(standalone))
            self.assertEqual(renamed.returncode, 0, renamed.stderr)
            self.assertEqual(len(json.loads(renamed.stdout)['edits']), 2)

    def test_bare_type_alias_in_expressions_and_declaration_headers(self):
        example = ROOT / 'examples/modules/bare-type/Main.fib'
        result = run('run', '--source-dir', str(example.parent), str(example))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, 'bare Type\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            source = example.read_text()
            path.write_text(source)
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn('data Optional (0 A : Type) : Type where', formatted.stdout)
            self.assertIn('data Higher : Type 1 where', formatted.stdout)
            lines = source.splitlines()
            row = next(index + 1 for index, line in enumerate(lines) if 'data Optional' in line)
            column = lines[row - 1].index('Type') + 1
            reference = run('reference', str(row), str(column), str(path))
            self.assertEqual(reference.returncode, 0, reference.stderr)
            info = json.loads(reference.stdout)['reference']
            self.assertEqual(info['name'], 'Type')
            self.assertTrue(any('Bare Type means Type 0' in line for line in info['lines']))
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(run('run', '--source-dir', directory, str(path)).stdout, 'bare Type\n')
            for bad in [source.replace('data Higher : Type 1 where', 'data Higher : Type 1234567 where'),
                        source.replace('record Wrap (0 A : Type) : Type where', 'record Wrap (0 A : Type) : Type 1234567 where'),
                        source.replace('interface Identity (0 A : Type) : Type where', 'interface Identity (0 A : Type) : Type 1234567 where')]:
                path.write_text(bad)
                result = run('check', '--source-dir', directory, str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('Universe level requires', result.stderr)
            path.write_text('0 main : Type\nmain = Type\n')
            self.assertNotEqual(run('check', '--erased', str(path)).returncode, 0)
            path.write_text('0 main : Type 1\nmain = Type\n')
            self.assertEqual(run('check', '--erased', str(path)).returncode, 0)
            path.write_text('Type unknown')
            error = run('check', '--erased', str(path))
            self.assertNotEqual(error.returncode, 0)
            self.assertIn('Unbound', error.stdout + error.stderr)
            self.assertNotIn('Parsing:', error.stdout + error.stderr)

    def test_multi_field_data_case(self):
        fixture = ROOT / 'examples/modules/multi-field-case/Main.fib'
        source = fixture.read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'customer ada@example.com\nstaff bob\ncarol\nabcd\nempty\ncustomer dave\nguest\n')
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(project('run').stdout, result.stdout)
            # Wrong arity, a constructor of another type, a missing or duplicate
            # constructor, and an unconsumed linear field are all rejected.
            for changed in [
                source.replace('  Customer email password => appendString "customer " email', '  Customer email => email', 1),
                source.replace('  Customer email password => appendString "customer " email', '  Customer email password extra => email', 1),
                source.replace('  Customer email password => appendString "customer " email\n', '', 1),
                source.replace('  Staff email => appendString "staff " email', '  Customer email password => email\n  Staff email => email', 1),
                source.replace('appendString item (appendString note (appendString count sku))', 'appendString item (appendString note count)', 1),
            ]:
                path.write_text(changed)
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertEqual(rejected.stdout, '')
            other = ('module Main\ndata User : Type where\n  Guest : User\n  Customer : (email : String) -> (password : String) -> User\n'
                     'data Other : Type where\n  Nope : Other\n  Pair : (a : String) -> (b : String) -> Other\n'
                     'f : User -> Bool\nf u = case u of\n  Guest => True\n  Pair a b => False\n'
                     'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(other)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('does not match the scrutinee type and shape', rejected.stdout + rejected.stderr)
            # An expected dependent result type selects the motive, with two and
            # three fields.
            dependent = ('module Main\ndata Triple : Type where\n  Mk : (a : String) -> (b : String) -> (c : String) -> Triple\n  None : Triple\n'
                         '0 Q : (0 t : Triple) -> Type 1\nQ t = case t of\n  Mk a b c => (String : Type 1)\n  None => (Bool : Type 1)\n'
                         'k : (1 t : Triple) -> Q t\nk t = case t of\n  Mk a b c => appendString a (appendString b c)\n  None => True\n'
                         'main : IO Unit\nmain = putStrLn (k (Mk "1" "2" "3"))\n')
            path.write_text(dependent)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, '123\n')

    def test_multi_field_clause_patterns_and_wildcard(self):
        header = ('module Main\ndata User : Type where\n  Guest : User\n'
                  '  Customer : (email : String) -> (password : String) -> User\n  Staff : (email : String) -> User\n'
                  'data Order : Type where\n  Empty : Order\n'
                  '  Line : (1 item : String) -> (1 note : String) -> Order\n')
        main = 'main : IO Unit\nmain = putStrLn (describe (Customer "ada" "pw"))\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            clauses = ('describe : (1 user : User) -> String\n'
                       'describe (Customer e p) = appendString "customer " e\n'
                       'describe Guest = "guest"\ndescribe Staff e = e\n')
            path.write_text(header + clauses + main)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'customer ada\n')
            formatted = run('format', str(path))
            self.assertEqual(formatted.stdout, header + clauses + main)
            # A lone parenthesized equation is still not a clause group.
            path.write_text(header + 'describe : User -> String\ndescribe (Customer e p) = e\n' + main)
            rejected = project('check')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('must be names', rejected.stdout + rejected.stderr)
            for bad in ['describe (Customer e) = e', 'describe (Customer e e) = e', 'describe () = e']:
                path.write_text(header + 'describe : User -> String\n' + bad + '\ndescribe Guest = "g"\ndescribe Staff e = e\n' + main)
                self.assertNotEqual(project('check').returncode, 0, bad)
            # `_` covers an unrestricted multi-field constructor but cannot drop linear fields.
            path.write_text(header + 'isGuest : User -> Bool\nisGuest Guest = True\nisGuest _ = False\n' + 'main : IO Unit\nmain = putStrLn "x"\n')
            self.assertEqual(project('check').returncode, 0)
            for linear in ['isEmpty Empty = True\nisEmpty _ = False\n', 'isEmpty Empty = True\nisEmpty other = False\n']:
                path.write_text(header + 'isEmpty : (1 order : Order) -> Bool\n' + linear + 'main : IO Unit\nmain = putStrLn "x"\n')
                rejected = project('check')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertIn('Binder usage', rejected.stdout + rejected.stderr)
            # A named catch-all rebuilds the multi-field value from unrestricted fields.
            path.write_text(header + 'describe : User -> String\ndescribe Staff e = e\ndescribe other = "other"\n'
                            + 'main : IO Unit\nmain = putStrLn (describe (Customer "a" "b"))\n')
            named = project('run')
            self.assertEqual(named.returncode, 0, named.stdout + named.stderr)
            self.assertEqual(named.stdout, 'other\n')
            # Arity is reported precisely.
            path.write_text(header + 'f : User -> Bool\nf u = case u of\n  Guest => True\n  Customer e => False\n  Staff e => True\n' + 'main : IO Unit\nmain = putStrLn "x"\n')
            rejected = project('check')
            self.assertIn('has 2 field(s) but the pattern binds 1', rejected.stdout + rejected.stderr)

    def test_inferred_data_case_motives(self):
        fixture = ROOT / 'examples/modules/direct-data-case/Main.fib'
        source = fixture.read_text().replace(' return (\\(0 self : Sum String Bool) => String)', '').replace(' return (\\(0 self : Sum A B) => C)', '')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            path.write_text(source)
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'L: hello\nR: yes\nno\n')
            target = json.loads(run('definition', '10', '37', str(path)).stdout)['definition']
            self.assertEqual((target['start']['line'], target['start']['column']), (10, 8))
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, result.stdout)
            different = source.replace('  Left value => appendString prefix value', '  Left value => True', 1)
            path.write_text(different)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertTrue(rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            for changed in [
                source.replace('  Left value => appendString prefix value\n', '', 1),
                source.replace('  Left value => appendString prefix value', '  Right value => appendString prefix value', 1),
                source.replace('  Left value => appendString prefix value', '  Left value => value', 1),
                source.replace('  Left value => appendString prefix value', '  Left value => appendString prefix (appendString prefix value)', 1),
                source.replace('  Left value => appendString prefix value', '   Left value => appendString prefix value', 1),
            ]:
                path.write_text(changed)
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertEqual(rejected.stdout, '')
            erased = ('module Main\ndata Secret : Type where\n  Empty : Secret\n  SecretValue : (0 flag : Bool) -> Secret\n'
                      'reveal : (1 secret : Secret) -> Bool\nreveal secret = case secret of\n'
                      '  Empty => False\n  SecretValue flag => flag\nmain : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(erased)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Beta-equivalent results normalize through the guarded converter,
            # even when no equation-expected type is available.
            convertible = ('module Main\ndata Choice : Type where\n  First : Choice\n  Second : Choice\n'
                           'select : (left : (\\(0 A : Type) => A) String) -> (right : String) -> (1 choice : Choice) -> String\n'
                           'select = \\(left : (\\(0 A : Type) => A) String) => \\(right : String) => \\(1 choice : Choice) => case choice of\n  First => left\n  Second => right\n'
                           'main : IO Unit\nmain = putStrLn (select "ok" "ok" First)\n')
            path.write_text(convertible)
            converted = project('run')
            self.assertEqual(converted.returncode, 0, converted.stdout + converted.stderr)
            self.assertEqual(converted.stdout, 'ok\n')
            path.write_text(convertible.replace('case choice of', 'case choice return (\\(0 self : Choice) => String) of'))
            explicit = project('run')
            self.assertEqual(explicit.returncode, 0, explicit.stdout + explicit.stderr)
            self.assertEqual(explicit.stdout, 'ok\n')
            # Payload-dependent branch types cannot be turned into a constant motive.
            dependent_payload = ('module Main\ndata Packed : Type 1 where\n  Value : (0 A : Type) -> Packed\n  Empty : Packed\n'
                                 'bad : (f : (0 A : Type) -> A) -> (1 item : Packed) -> String\n'
                                 'bad = \\(f : (0 A : Type) -> A) => \\(1 item : Packed) => case item of\n  Value A => f A\n  Empty => "nothing"\n'
                                 'main : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(dependent_payload)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertTrue(rejected.stderr)
            self.assertEqual(rejected.stdout, '')
            # The declared result supplies an expected dependent motive in
            # both named equations and explicitly annotated lambdas.
            dependent = (ROOT / 'examples/modules/direct-data-case-dependent/Main.fib').read_text()
            path.write_text(dependent)
            self.assertEqual(project('run').stdout, 'first\n')
            no_expected = dependent.replace('choose choice = case choice of', 'choose = \\(1 choice : Select) => case choice of')
            path.write_text(no_expected)
            self.assertEqual(project('run').stdout, 'first\n')
            path.write_text(no_expected.replace('case choice of', 'case choice return (\\(0 self : Select) => Family self) of'))
            self.assertEqual(project('run').stdout, 'first\n')
            # Normalizing the scrutinee once reveals the index in the expected
            # family; the selected candidate is checked against the original type.
            arbitrary = dependent.replace('choose choice = case choice of', 'choose choice = case ((\\(1 x : Select) => x) choice) of')
            path.write_text(arbitrary)
            self.assertEqual(project('run').stdout, 'first\n')
            neutral = dependent.replace('choose : (1 choice : Select)', 'choose : (f : (1 x : Select) -> Select) -> (1 choice : Select)').replace('choose choice = case choice of', 'choose f choice = case (f choice) of').replace('choose First)', 'choose (\\(1 x : Select) => x) First)')
            path.write_text(neutral)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Large expected results do not impose the abstraction limit on a
            # valid constant candidate; truly dependent abstraction is bounded.
            chain = ' -> '.join(['String'] * 131)
            huge = f'({chain}) -> ({chain})'
            large_constant = ('module Main\ndata Choice : Type where\n  First : Choice\n  Second : Choice\n'
                              f'result : (1 choice : Choice) -> ((\\(0 A : Type) => Bool) ({huge}))\n'
                              'result choice = case choice of\n  First => True\n  Second => False\n'
                              'main : IO Unit\nmain = if result First then putStrLn "ok" else putStrLn "no"\n')
            path.write_text(large_constant)
            large_result = project('run')
            self.assertEqual(large_result.returncode, 0, large_result.stdout + large_result.stderr)
            self.assertEqual(large_result.stdout, 'ok\n')
            # A large expected type is not cloned through the checking-mode let.
            nested_lets = 'result choice = ' + 'let (0 t : Type) = Bool in ' * 8 + 'case choice of'
            path.write_text(large_constant.replace('result choice = case choice of', nested_lets))
            self.assertEqual(project('run').stdout, 'ok\n')
            large_dependent = dependent.replace('-> Family choice\nchoose choice', f'-> ((\\(0 A : Type) => Family choice) ({huge}))\nchoose choice')
            path.write_text(large_dependent)
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Expected data-case result exceeds 512 nodes', rejected.stderr)
            path.write_text(large_dependent.replace('choose choice = case choice of', 'choose choice = case choice return (\\(0 self : Select) => Family self) of'))
            self.assertEqual(project('run').stdout, 'first\n')
            # A neutral family may reduce to the same result in both branches;
            # constant inference must not preclude the expected dependent motive.
            additional = ('\n0 Uniform : (0 choice : Select) -> Type 1\n'
                          'Uniform = \\(0 choice : Select) => case choice return (\\(0 self : Select) => Type 1) of\n'
                          '  First => (Bool : Type 1)\n  Second => (Bool : Type 1)\n'
                          'uniform : (1 choice : Select) -> Uniform choice\nuniform choice = case choice of\n  First => True\n  Second => False\n'
                          # Constant motive retains the ambient choice when the
                          # dependent abstraction would incorrectly refine arg.
                          'keep : (1 choice : Select) -> (arg : Family choice) -> Family choice\n'
                          'keep choice arg = case choice of\n  First => arg\n  Second => arg\n'
                          # Choice is older than unused, and occurs below a Pi binder.
                          'fun : (1 choice : Select) -> (unused : String) -> (1 x : Family choice) -> Family choice\n'
                          'fun choice unused = case choice of\n  First => \\(1 x : String) => x\n  Second => \\(1 x : Bool) => x\n')
            guided = dependent.replace('\nmain : IO Unit', additional + '\nmain : IO Unit').replace('main = putStrLn (choose First)', 'main = putStrLn (fun First "unused" "works")')
            path.write_text(guided)
            guided_result = project('run')
            self.assertEqual(guided_result.returncode, 0, guided_result.stdout + guided_result.stderr)
            self.assertEqual(guided_result.stdout, 'works\n')
            under_binder = guided.replace('fun choice unused = case choice of', 'fun choice unused = case ((\\(1 x : Select) => x) choice) of')
            path.write_text(under_binder)
            inferred = project('run')
            self.assertEqual(inferred.returncode, 0, inferred.stdout + inferred.stderr)
            self.assertEqual(inferred.stdout, 'works\n')
            path.write_text(guided.replace('First => \\(1 x : String) => x', 'First => \\(1 x : Bool) => x'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            path.write_text(guided.replace('Second => \\(1 x : Bool) => x', 'Second => \\(1 x : Bool) => True'))
            dropped = project('run')
            self.assertNotEqual(dropped.returncode, 0)
            self.assertEqual(dropped.stdout, '')
            path.write_text(guided.replace('uniform : (1 choice : Select)', 'uniform : (0 choice : Select)'))
            erased_use = project('run')
            self.assertNotEqual(erased_use.returncode, 0)
            self.assertEqual(erased_use.stdout, '')
            # Nested inferred cases preserve outer variables and shadowed binders.
            nested = ('module Main\ndata Message : Type where\n  Missing : Message\n  Text : (1 value : String) -> Message\n'
                      'combine : (1 first : Message) -> (1 second : Message) -> String\n'
                      'combine first second = case first of\n'
                      '  Missing => case second of\n    Missing => "none"\n    Text value => value\n'
                      '  Text value => case second of\n    Missing => value\n    Text other => appendString value other\n'
                      'main : IO Unit\nmain = putStrLn (combine (Text "a") (Text "b"))\n')
            path.write_text(nested)
            nested_result = project('run')
            self.assertEqual(nested_result.returncode, 0, nested_result.stdout + nested_result.stderr)
            self.assertEqual(nested_result.stdout, 'ab\n')

    def test_dependent_motives_across_expression_contexts(self):
        source = (ROOT / 'examples/modules/direct-data-case-dependent/Main.fib').read_text()
        target = '((\\(1 x : Select) => x) choice)'
        arbitrary = source.replace('-> Family choice\nchoose choice', f'-> Family {target}\nchoose choice').replace('choose choice = case choice of', f'choose choice = case {target} of')
        ascribed = source.replace('choose choice = case choice of', 'choose choice = (case choice of').replace('  Second => True\n\nmain', '  Second => True : Family choice)\n\nmain')
        let_body = source.replace('choose choice = case choice of', 'choose choice = let (0 ignored : Type) = String in case choice of')
        let_value = source.replace('choose choice = case choice of\n  First => "first"\n  Second => True', 'choose choice =\n  let (1 answer : Family choice) = case choice of\n    First => "first"\n    Second => True\n  in answer')
        identity = 'identity : (0 T : Type 1) -> (1 value : T) -> T\nidentity T value = value\n\n'
        applied = source.replace('choose :', identity + 'choose :').replace('choose choice = case choice of', 'choose choice = identity (Family choice) (case choice of').replace('  Second => True\n\nmain', '  Second => True)\n\nmain')
        nested_function = ('\nchoose2 : (1 outer : Select) -> (1 inner : Select) -> Family inner\n'
                           'choose2 outer inner = case outer of\n'
                           '  First => case inner of\n    First => "first"\n    Second => True\n'
                           '  Second => case inner of\n    First => "first"\n    Second => True\n')
        nested = source.replace('\nmain : IO Unit', nested_function + '\nmain : IO Unit').replace('main = putStrLn (choose First)', 'main = putStrLn (choose2 First First)')
        nested_explicit = nested.replace('case outer of', 'case outer return (\\(0 self : Select) => Family inner) of')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            for label, program in [('arbitrary', arbitrary), ('ascription', ascribed), ('let body', let_body), ('let value', let_value), ('application argument', applied), ('nested', nested), ('nested explicit', nested_explicit)]:
                with self.subTest(label=label):
                    path.write_text(program)
                    result = run('run', '--source-dir', directory, str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stdout, 'first\n')
            # Arbitrary-subterm matching has an explicit work budget; exhaustion
            # does not prevent an independently checked explicit motive.
            large_target = '((\\(0 s : String) => \\(1 x : Select) => x) "' + ('x' * 600) + '" choice)'
            costly = source.replace('-> Family choice\nchoose choice', f'-> Family {large_target}\nchoose choice').replace('choose choice = case choice of', f'choose choice = case {large_target} of')
            path.write_text(costly)
            rejected = run('run', '--source-dir', directory, str(path))
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('abstraction work budget exhausted', rejected.stderr)
            path.write_text(costly.replace(f'case {large_target} of', f'case {large_target} return (\\(0 self : Select) => Family self) of'))
            explicit = run('run', '--source-dir', directory, str(path))
            self.assertEqual(explicit.returncode, 0, explicit.stdout + explicit.stderr)
            self.assertEqual(explicit.stdout, 'first\n')
            path.write_text(nested.replace('    Second => True', '    Second => "bad"', 1))
            bad = run('run', '--source-dir', directory, str(path))
            self.assertNotEqual(bad.returncode, 0)
            self.assertEqual(bad.stdout, '')

    def test_expected_motives_in_typed_do_unit_and_infix(self):
        source = (ROOT / 'examples/modules/direct-data-case-dependent/Main.fib').read_text()
        unit_case = source.replace('choose choice = case choice of', 'choose choice = case () of () => case choice of')
        operators = ('pick : (0 T : Type 1) -> (1 first : T) -> (second : String) -> T\n'
                     'pick T first second = first\n'
                     'pickRight : (0 T : Type 1) -> (first : String) -> (1 second : T) -> T\n'
                     'pickRight T first second = second\n\n')
        infix_base = source.replace('choose :', operators + 'choose :')
        infix_left = infix_base.replace('choose choice = case choice of\n  First => "first"\n  Second => True', 'choose choice = (case choice of\n  First => "first"\n  Second => True) `pick (Family choice)` "unused"')
        infix_right = infix_base.replace('choose choice = case choice of\n  First => "first"\n  Second => True', 'choose choice = "unused" `pickRight (Family choice)` (case choice of\n  First => "first"\n  Second => True)')
        header = ('module Main\ndata Select : Type where\n  First : Select\n  Second : Select\n'
                  'choose : (0 F : (0 x : Select) -> Type) -> (first : F First) -> (second : F Second) -> (1 choice : Select) -> IO (F choice)\n')
        terminal = ('choose F first second choice = do (F choice)\n'
                    '  (1 text : String) <- pure String "log"\n  putStrLn text\n'
                    '  case choice of\n    First => pure (F First) first\n    Second => pure (F Second) second\n')
        do_let = ('choose F first second choice = do (F choice)\n'
                  '  let (1 answer : F choice) = case choice of\n    First => first\n    Second => second\n'
                  '  pure (F choice) answer\n')
        main = ('main : IO Unit\nmain = do\n'
                '  (1 text : String) <- choose (\\(0 x : Select) => String) "first" "second" First\n'
                '  putStrLn text\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            for label, program, output in [('unit case', unit_case, 'first\n'), ('infix left', infix_left, 'first\n'), ('infix right', infix_right, 'first\n'), ('typed do terminal', header + terminal + main, 'log\nfirst\n'), ('typed do let', header + do_let + main, 'first\n')]:
                with self.subTest(label=label):
                    path.write_text(program)
                    result = run('run', '--source-dir', directory, str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stdout, output)
                    formatted = run('format', str(path))
                    self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(header + terminal.replace('  putStrLn text', '  putStrLn (appendString text text)') + main)
            rejected = run('run', '--source-dir', directory, str(path))
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            path.write_text(header + terminal.replace('    Second => pure (F Second) second', '  Second => pure (F Second) second') + main)
            malformed = run('run', '--source-dir', directory, str(path))
            self.assertNotEqual(malformed.returncode, 0)
            self.assertEqual(malformed.stdout, '')
            nested = ('module Main\nmain : IO Unit\nmain = do\n  do\n    putStrLn "nested"\n')
            path.write_text(nested)
            rejected = run('run', '--source-dir', directory, str(path))
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Nested do blocks are not supported', rejected.stderr)
            self.assertEqual(rejected.stdout, '')

    def test_motive_probe_branch_budget_is_admitted_without_exponential_planning(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            data = 'module Main\ndata Choice : Type where\n  A : Choice\n  B : Choice\n'
            values = 'v0 : String\nv0 = "x"\n' + ''.join(f'v{i} : String\nv{i} = appendString v{i-1} v{i-1}\n' for i in range(1, 10))
            body = ('choose : (1 x : Choice) -> String\nchoose x = case ((\\(1 y : Choice) => y) x) of\n'
                    '  A => v9\n  B => v9\nmain : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(data + values + body)
            accepted = run('run', '--source-dir', directory, str(path))
            self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
            self.assertEqual(accepted.stdout, 'never\n')
            depth = 15
            nested = data + 'choose : (1 x : Choice) -> String\nchoose x = case x of\n'
            for level in range(depth):
                nested += ' ' * (2 * (level + 1)) + 'A => case x of\n'
            nested += ' ' * (2 * (depth + 1)) + 'A => "ok"\n'
            nested += ' ' * (2 * (depth + 1)) + 'B => "ok"\n'
            for level in reversed(range(depth)):
                nested += ' ' * (2 * (level + 1)) + 'B => "ok"\n'
            path.write_text(nested + 'main : IO Unit\nmain = putStrLn "never"\n')
            rejected = run('run', '--source-dir', directory, str(path))
            self.assertNotEqual(rejected.returncode, 0)
            self.assertIn('Expanded core construction budget exhausted', rejected.stderr)
            self.assertEqual(rejected.stdout, '')

    def test_ordinary_lets_do_not_consume_expected_clone_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for module in range(7):
                definitions = ''.join(f'v{i} : Bool\nv{i} = let (0 t : Type) = Bool in True\n' for i in range(60))
                (root / f'M{module}.fib').write_text(f'module M{module}\n' + definitions)
            entry = root / 'Main.fib'
            entry.write_text('module Main\n' + ''.join(f'import M{i}\n' for i in range(7)) + 'main : IO Unit\nmain = putStrLn "ok"\n')
            result = run('run', '--source-dir', directory, str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'ok\n')

    def test_direct_nonrecursive_data_cases(self):
        fixture = ROOT / 'examples/modules/direct-data-case/Main.fib'
        source = fixture.read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            def project(command):
                return run(command, '--source-dir', directory, str(path))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'L: hello\nR: yes\nno\n')
            # The actual authored constructor and field-binder targets, not invented spans.
            constructor = json.loads(run('definition', '10', '3', str(path)).stdout)['definition']
            binder = json.loads(run('definition', '10', '37', str(path)).stdout)['definition']
            self.assertEqual((constructor['start']['line'], constructor['start']['column']), (4, 3))
            self.assertEqual((binder['start']['line'], binder['start']['column']), (10, 8))
            formatted = run('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(path)).returncode, 0)
            self.assertEqual(project('run').stdout, 'L: hello\nR: yes\nno\n')
            # Exhaustiveness, identity, arity and linear usage remain checker boundaries.
            invalid = [
                source.replace('  Left value => appendString prefix value\n', ''),
                source.replace('  Left value => appendString prefix value', '  Right value => appendString prefix value'),
                source.replace('  Left value => appendString prefix value', '  Unknown value => appendString prefix value'),
                source.replace('  Left value => appendString prefix value', '  Left => prefix'),
                source.replace('  Left value => appendString prefix value', '  Left value => value'),
                source.replace('  Left value => appendString prefix value', '  Left value => appendString prefix (appendString prefix value)'),
                source.replace('  Left value => appendString prefix value', '   Left value => appendString prefix value'),
                source.replace('=> String) of\n  Right flag', '=> Bool) of\n  Right flag', 1),
            ]
            for program in invalid:
                with self.subTest(program=program[:180]):
                    path.write_text(program)
                    rejected = project('run')
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                    self.assertEqual(rejected.stdout, '')
            grouped = ('module Main\n\ndata Message : Type 0 where\n  Missing : Message\n  Text : (1 value : String) -> Message\n\n'
                       'main : IO Unit\nmain = putStrLn (case Text "inside" return (\\(0 self : Message) => String) of\n'
                       '  Missing => "missing"\n  Text value => value)\n')
            path.write_text(grouped)
            nested = project('run')
            self.assertEqual(nested.returncode, 0, nested.stdout + nested.stderr)
            self.assertEqual(nested.stdout, 'inside\n')
            path.write_text(grouped.replace('Text value => value)', 'Text value => value : String)'))
            ascribed = project('run')
            self.assertEqual(ascribed.returncode, 0, ascribed.stdout + ascribed.stderr)
            self.assertEqual(ascribed.stdout, 'inside\n')
            nestedSource = ('module Main\n\ndata Message : Type 0 where\n  Missing : Message\n  Text : (1 value : String) -> Message\n\n'
              'combine : (1 first : Message) -> (1 second : Message) -> String\n'
              'combine = \\(1 first : Message) => \\(1 second : Message) => case first return (\\(0 self : Message) => String) of\n'
              '  Missing => case second return (\\(0 self : Message) => String) of\n'
              '    Missing => "none"\n    Text value => value\n'
              '  Text left => case second return (\\(0 self : Message) => String) of\n'
              '    Missing => left\n    Text right => appendString left right\n\n'
              'main : IO Unit\nmain = putStrLn (combine (Text "a") (Text "b"))\n')
            path.write_text(nestedSource)
            nested = project('run')
            self.assertEqual(nested.returncode, 0, nested.stdout + nested.stderr)
            self.assertEqual(nested.stdout, 'ab\n')
            dependent = ROOT / 'examples/modules/direct-data-case-dependent/Main.fib'
            dependentResult = run('run', '--source-dir', str(dependent.parent), str(dependent))
            self.assertEqual(dependentResult.returncode, 0, dependentResult.stdout + dependentResult.stderr)
            self.assertEqual(dependentResult.stdout, 'first\n')
            alias = source.replace('\nrender :', '\nAlias : (0 A : Type 0) -> (0 B : Type 0) -> (1 value : A) -> Sum A B\nAlias = Left\n\nrender :', 1)
            path.write_text(alias.replace('  Left value => appendString prefix value', '  Alias value => appendString prefix value', 1))
            aliased = project('run')
            self.assertEqual(aliased.returncode, 0, aliased.stdout + aliased.stderr)
            self.assertEqual(aliased.stdout, 'L: hello\nR: yes\nno\n')
            # A checked but wrong nominal constructor cannot act as an arm label.
            foreign = source.replace('render :', 'data Other : Type 0 where\n  OtherValue : (1 item : String) -> Other\n\nrender :', 1)
            path.write_text(foreign.replace('  Left value => appendString prefix value', '  OtherValue value => appendString prefix value'))
            self.assertNotEqual(project('check').returncode, 0)
            # Parameterized wildcard fields and erased use are checked, not silently ignored.
            erased = ('module Main\n\ndata Secret : Type 0 where\n  Empty : Secret\n  SecretValue : (0 flag : Bool) -> Secret\n\n'
                      'reveal : (1 secret : Secret) -> Bool\nreveal = \\(1 secret : Secret) => case secret return (\\(0 self : Secret) => Bool) of\n'
                      '  Empty => False\n  SecretValue flag => flag\n\nmain : IO Unit\nmain = putStrLn "never"\n')
            path.write_text(erased)
            self.assertNotEqual(project('run').returncode, 0)
            self.assertEqual(project('run').stdout, '')

    def test_qualified_imported_data_case_across_local_packages(self):
        import shutil
        fixtures = ROOT / 'examples/packages'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixtures / 'sum-library', root / 'sum-library')
            shutil.copytree(fixtures / 'sum-client', root / 'sum-client')
            app = root / 'sum-client'
            manifest = app / 'fibril.yaml'
            main = app / 'src/Main.fib'
            library = root / 'sum-library/src/Data/Sum.fib'
            original = main.read_text()
            def project(command):
                return run(command, '--package', str(manifest))
            result = project('run')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'L: hello\nR: yes\n')
            formatted = run('format', str(main))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            main.write_text(formatted.stdout)
            self.assertEqual(run('format', '--check', str(main)).returncode, 0)
            self.assertEqual(project('run').stdout, 'L: hello\nR: yes\n')
            main.write_text(original)
            for broken in [original.replace('import Data.Sum\n', ''),
                           original.replace('Data.Sum.Left text =>', 'Data.Sum.Missing text =>'),
                           original.replace('Data.Sum.Left text =>', 'Data..Sum.Left text =>'),
                           original.replace('Data.Sum.Left text =>', 'data.Sum.Left text =>'),
                           original.replace('Data.Sum.Left text =>', 'Data.Sum.\n  Left text =>'),
                           original.replace('Data.Sum.Left text =>', 'Data.Sum.Right text =>'),
                           original.replace('  Data.Sum.Left text => appendString prefix text', '  Data.Sum.Left => prefix')]:
                main.write_text(broken)
                rejected = project('run')
                self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
                self.assertEqual(rejected.stdout, '')
            main.write_text(original)
            saved = library.read_text()
            alias = ('\nalias : (0 A : Type 0) -> (0 B : Type 0) -> (1 value : A) -> Sum A B\n'
                     'alias = Left\n')
            library.write_text(saved + '\nexport\n' + alias)
            main.write_text(original.replace('Data.Sum.Left text =>', 'Data.Sum.alias text =>'))
            public_alias = project('run')
            self.assertEqual(public_alias.returncode, 0, public_alias.stdout + public_alias.stderr)
            library.write_text(saved + alias)
            private_alias = project('run')
            self.assertNotEqual(private_alias.returncode, 0)
            self.assertEqual(private_alias.stdout, '')
            main.write_text(original)
            library.write_text(saved.replace('export\ndata Sum', 'data Sum'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            library.write_text(saved)
            # Package permission is checked before matching, even with a transitive dependency.
            bridge = root / 'bridge'
            (bridge / 'src').mkdir(parents=True)
            (bridge / 'fibril.yaml').write_text('schema: 1\nname: bridge\nmodule-prefix: Bridge\nsource-dir: src\nfoundation: de-morgan\ndependencies:\n  sum-library:\n    path: ../sum-library\n')
            manifest.write_text(manifest.read_text().replace('  sum-library:\n    path: ../sum-library', '  bridge:\n    path: ../bridge'))
            rejected = project('run')
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            # Single-root editor services find the real imported constructor token.
            single = root / 'single'
            (single / 'Data').mkdir(parents=True)
            entry = single / 'Main.fib'
            entry.write_text(original)
            target = single / 'Data/Sum.fib'
            target.write_text(saved)
            definition = run('definition', '--source-dir', str(single), '--entry', str(entry), '6', '12', str(entry))
            self.assertEqual(definition.returncode, 0, definition.stdout + definition.stderr)
            found = json.loads(definition.stdout)['definition']
            self.assertEqual(Path(found['path']).resolve(), target.resolve())
            self.assertEqual((found['range']['start']['line'], found['range']['start']['column']), (7, 3))
            binder = run('definition', '7', '45', str(entry))
            self.assertEqual(binder.returncode, 0, binder.stderr)
            self.assertEqual(json.loads(binder.stdout)['definition']['start']['column'], 17)

    def test_non_church_sum_library_checks_and_runs_suite(self):
        package = ROOT / "examples/packages/sum-library/fibril.yaml"
        checked = run("check", "--package", str(package))
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        tested = run("test", "--package", str(package))
        self.assertEqual(tested.returncode, 0, tested.stdout + tested.stderr)
        self.assertIn("Tests: passed", tested.stdout)
        # Run the same authored suite against a deliberately inverted assertion.
        with tempfile.TemporaryDirectory() as directory:
            import shutil
            fixture = Path(directory) / "sum-library"
            shutil.copytree(package.parent, fixture)
            suite = fixture / "src/Data/Sum/Tests.fib"
            suite.write_text(suite.read_text().replace('"left" then equalString', '"wrong" then equalString'))
            failed = run("test", "--package", str(fixture / "fibril.yaml"))
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("Tests: failed", failed.stderr)

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


class UnqualifiedImportsTests(unittest.TestCase):
    def test_alias_ambiguity_reports_canonical_definitions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ['A', 'B']:
                (root / (name + '.fib')).write_text(
                    'module ' + name + '\nexport\n'
                    'keep : {0 T : Type} -> (1 x : T) -> T\nkeep T x = x\n'
                    'export\ndata Choice : Type where\n  Yes : Choice\n  No : Choice\n')
            main = root / 'Main.fib'

            def check(imports, body):
                main.write_text('module Main\n' + imports + '\nmain : IO Unit\nmain = ' + body + '\n')
                return run_cli('check', '--source-dir', directory, str(main), timeout=120)

            for body in ['putStrLn (keep "ok")', 'putStrLn (keep {String} "ok")',
                         'putStrLn (case A.Yes of\n  Yes => "yes"\n  A.No => "no")']:
                with self.subTest(body=body):
                    result = check('import A as X\nimport B as Y', body)
                    self.assertNotEqual(result.returncode, 0)
                    short = 'Yes' if 'case' in body else 'keep'
                    self.assertIn('candidates: A.' + short + ', B.' + short + ';', result.stderr)
                    self.assertNotIn('X.' + short, result.stderr)
                    self.assertNotIn('Y.' + short, result.stderr)

            for body in ['putStrLn (keep "ok")', 'putStrLn (keep {String} "ok")',
                         'putStrLn (X.keep {String} (A.keep "ok"))',
                         'putStrLn (case X.Yes of\n  Yes => "yes"\n  No => "no")']:
                with self.subTest(unique=body):
                    result = check('import A as X', body)
                    self.assertEqual(result.returncode, 0, result.stderr)

    def test_lookup_shadowing_ambiguity_and_visibility(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ngreet : String -> String\ngreet = \\(x : String) => appendString "A" x\nsecret : String\nsecret = "secret"\n')
            (root / 'B.fib').write_text('module B\nexport\ngreet : String -> String\ngreet = \\(x : String) => appendString "B" x\n')
            main = root / 'Main.fib'
            def execute(source):
                main.write_text(source)
                return run_cli('run', '--source-dir', directory, str(main), timeout=120)
            result = execute('module Main\nimport A\nmain : IO Unit\nmain = putStrLn (greet "!")\n')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'A!\n')
            nav = run_cli('definition', '--source-dir', directory, '--entry', str(main), '4', '18', str(main))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(Path(json.loads(nav.stdout)['definition']['path']).name, 'A.fib')
            result = execute('module Main\nimport A\nimport A\nmain : IO Unit\nmain = putStrLn (greet "!")\n')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Duplicate direct import', result.stderr)
            result = execute('module Main\nimport A\nimport B\nmain : IO Unit\nmain = putStrLn (greet "!")\n')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Ambiguous imported name greet', result.stderr)
            result = execute('module Main\nimport A\nimport B\nmain : IO Unit\nmain = putStrLn (A.greet "!")\n')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'A!\n')
            result = execute('module Main\nimport A\ngreet : String -> String\ngreet = \\(x : String) => appendString "local" x\nmain : IO Unit\nmain = putStrLn (greet "!")\n')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'local!\n')
            result = execute('module Main\nimport A\nmain : IO Unit\nmain = putStrLn secret\n')
            self.assertNotEqual(result.returncode, 0)

    def test_navigation_in_record_and_interface_fields(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\n0 Name : Type\nName = String\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nrecord Person : Type where\n  constructor MkPerson\n  value : Name\ninterface Describe : Type where\n  constructor MkDescribe\n  render : (value : Name) -> String\nmain : IO Unit\nmain = putStrLn "ok"\n')
            for line, column in [('5', '12'), ('8', '21')]:
                result = run_cli('definition', '--source-dir', directory, '--entry', str(main), line, column, str(main), timeout=120)
                self.assertEqual(result.returncode, 0, result.stderr)
                packet = json.loads(result.stdout)
                self.assertIsNotNone(packet['definition'], result.stdout)
                self.assertEqual(Path(packet['definition']['path']).name, 'A.fib')

    def test_interface_value_collision_reports_both_candidates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface Ops (0 T : Type) : Type where\n  constructor MkOps\n  op : (x : T) -> T\n')
            (root / 'B.fib').write_text('module B\nexport\n0 Ops : Type\nOps = String\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nimport B\nimplementation chosen : Ops String where\n  op = \\(x : String) => x\nmain : IO Unit\nmain = putStrLn "ok"\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Ambiguous imported interface Ops', result.stderr)
            self.assertIn('A.Ops', result.stderr)
            self.assertIn('B.Ops', result.stderr)

    def test_ambiguous_interface_reports_candidates_and_qualified_works(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ['A', 'B']:
                (root / (name + '.fib')).write_text('module ' + name + '\nexport\ninterface Ops (0 T : Type) : Type where\n  constructor MkOps\n  op : (x : T) -> T\n')
            main = root / 'Main.fib'
            source = 'module Main\nimport A\nimport B\nimplementation chosen : Ops String where\n  op = \\(x : String) => x\nmain : IO Unit\nmain = putStrLn "ok"\n'
            main.write_text(source)
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Ambiguous imported interface Ops', result.stderr)
            self.assertIn('A.Ops', result.stderr)
            self.assertIn('B.Ops', result.stderr)
            main.write_text(source.replace('chosen : Ops String', 'chosen : A.Ops String'))
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_local_type_shadow_does_not_reuse_imported_interface_schema(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface Ops (0 T : Type) : Type where\n  constructor MkOps\n  op : (x : T) -> T\n')
            (root / 'B.fib').write_text('module B\nexport\ninterface Other (0 T : Type) : Type where\n  constructor MkOther\n  different : (x : T) -> T\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nimport B\n0 Ops : (0 T : Type) -> Type\nOps = \\(0 T : Type) => B.Other T\nimplementation chosen : Ops String where\n  op = \\(x : String) => x\nmain : IO Unit\nmain = putStrLn "ok"\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Interface schema unavailable', result.stderr)

    def test_ambiguous_explicit_implicit_arguments_show_candidates(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ['A', 'B']:
                (root / (name + '.fib')).write_text('module ' + name + '\nexport\nkeep : {0 T : Type} -> (1 x : T) -> T\nkeep T x = x\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nimport B\nmain : IO Unit\nmain = putStrLn (keep {String} "x")\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Ambiguous imported name keep', result.stderr)
            self.assertIn('A.keep', result.stderr)
            self.assertIn('B.keep', result.stderr)

    def test_explicit_implicit_call_respects_local_shadowing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ['A', 'B']:
                (root / (name + '.fib')).write_text('module ' + name + '\nexport\nkeep : {0 T : Type} -> (1 x : T) -> T\nkeep T x = x\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nimport B\nkeep : String -> String\nkeep x = x\nmain : IO Unit\nmain = putStrLn (keep {String} "x")\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Explicit {arguments} require', result.stderr)
            self.assertNotIn('Ambiguous imported name', result.stderr)

    def test_ambiguous_import_does_not_fall_back_to_prelude(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ['A', 'B']:
                (root / (name + '.fib')).write_text('module ' + name + '\nexport\nputStrLn : String -> IO Unit\nputStrLn x = pure Unit ()\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nimport B\nmain : IO Unit\nmain = putStrLn "x"\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Ambiguous imported name putStrLn', result.stderr)

    def test_implicit_arguments_and_definition_navigation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nkeep : {0 A : Type} -> (1 x : A) -> A\nkeep A x = x\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A\nmain : IO Unit\nmain = putStrLn (keep "ok")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'ok\n')
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '4', '19', str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            packet = json.loads(result.stdout)
            self.assertEqual(Path(packet['definition']['path']).name, 'A.fib')

    def test_unqualified_interface_schema_and_direct_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface Ops (0 T : Type) : Type where\n  constructor MkOps\n  op : (x : T) -> T\n')
            (root / 'B.fib').write_text('module B\nimport A\nexport\nimplementation ops : Ops String where\n  op = \\(x : String) => x\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport B\nmain : IO Unit\nmain = putStrLn "ok"\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            main.write_text('module Main\nimport B\nx : Ops String\nx = ops\nmain : IO Unit\nmain = putStrLn "ok"\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unbound', result.stderr)

    def test_imported_constructor_patterns(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Choice.fib').write_text('module Choice\nexport\ndata Choice : Type where\n  Yes : Choice\n  No : Choice\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport Choice\nmain : IO Unit\nmain = putStrLn (case Yes return (\\(0 self : Choice) => String) of\n  Yes => "yes"\n  No => "no")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'yes\n')
            nav = run_cli('definition', '--source-dir', directory, '--entry', str(main), '5', '4', str(main))
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(Path(json.loads(nav.stdout)['definition']['path']).name, 'Choice.fib')

    def test_unqualified_implicit_metadata_and_reference(self):
        import shutil
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / 'examples/modules/implicit-arguments', root, dirs_exist_ok=True)
            main = root / 'Main.fib'
            main.write_text(main.read_text().replace('Utility.Identity.', ''))
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'queued: receipt\nexplicit type\nphantom type\nboth inferred\npartly explicit\n')
            # Syntax-only reference has no checked import context and must not
            # fabricate a bundled Prelude target for a possibly shadowed name.
            source = root / 'reference.fib'
            source.write_text('module Main\nimport Utility.Identity\nmain : IO Unit\nmain = putStrLn "x"\n')
            reference = run_cli('reference', '4', '9', str(source))
            self.assertEqual(reference.returncode, 0, reference.stderr)
            self.assertIsNone(json.loads(reference.stdout)['reference'])

    def test_unqualified_interface_block(self):
        import shutil
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / 'examples/modules/interface-blocks', root, dirs_exist_ok=True)
            instance = root / 'Instances/Text.fib'
            instance.write_text(instance.read_text().replace('Algebra.Semigroup String', 'Semigroup String')
                                .replace('Algebra.Monoid String', 'Monoid String'))
            result = run_cli('run', '--source-dir', directory, str(root / 'Main.fib'), timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


class RecursiveImportIntegrationTests(unittest.TestCase):
    def test_selective_alias_recursive_data_and_omitted_constructor(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Chain.fib').write_text('module Chain\nexport\ndata Chain : Type where\n  Empty : Chain\n  More : (1 rest : Chain) -> Chain\n')
            main = root / 'Main.fib'
            source = ('module Main\nimport Chain as C (Chain, Empty, More)\n'
                      'marks : (1 chain : C.Chain) -> String\nmarks chain = case chain of\n'
                      '  C.Empty => ""\n  C.More rest => appendString "!" (marks rest)\n'
                      'main : IO Unit\nmain = putStrLn (marks (C.More C.Empty))\n')
            main.write_text(source)
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, '!\n')
            nav = run_cli('definition', '--source-dir', directory, '--entry', str(main), '6', '39', str(main), timeout=120)
            self.assertEqual(nav.returncode, 0, nav.stderr)
            self.assertEqual(json.loads(nav.stdout)['definition']['range']['start']['line'], 4)
            main.write_text(source.replace('(Chain, Empty, More)', '(Chain, Empty)'))
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)

    def test_library_inventory_recursive_self_call_navigation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'src/Lib').mkdir(parents=True)
            (root / 'fibril.yaml').write_text('schema: 1\nname: lib\nmodule-prefix: Lib\nsource-dir: src\nfoundation: de-morgan\nmodules: [Lib.Chain]\ndependencies: {}\n')
            source = root / 'src/Lib/Chain.fib'
            source.write_text('module Lib.Chain\ndata Chain : Type where\n  Empty : Chain\n  More : (1 rest : Chain) -> Chain\nmarks : (1 chain : Chain) -> String\nmarks chain = case chain of\n  Empty => ""\n  More rest => appendString "!" (marks rest)\n')
            result = run_cli('definition', '--package', str(root / 'fibril.yaml'), '8', '35', str(source), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            target = json.loads(result.stdout)['definition']
            self.assertIsNotNone(target, result.stdout)
            self.assertEqual(Path(target['path']), source.resolve())
            self.assertEqual(target['range']['start']['line'], 6)


class ImportQualifierAliasTests(unittest.TestCase):
    def test_values_implicit_navigation_and_visibility(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nkeep : {0 T : Type} -> (1 x : T) -> T\nkeep T x = x\nsecret : String\nsecret = "no"\n')
            main = root / 'Main.fib'
            source = 'module Main\nimport A as X\nmain : IO Unit\nmain = putStrLn (X.keep {String} (A.keep "ok"))\n'
            main.write_text(source)
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'ok\n')
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '4', '21', str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']).name, 'A.fib')
            main.write_text(source.replace('X.keep {String} (A.keep "ok")', 'X.secret'))
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)

    def test_patterns_and_interface_schema(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ndata Choice : Type where\n  Yes : Choice\n  No : Choice\nexport\ninterface Ops (0 T : Type) : Type where\n  constructor MkOps\n  op : (x : T) -> T\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A as X\nimplementation chosen : X.Ops String where\n  op = \\(x : String) => x\nmain : IO Unit\nmain = putStrLn (case X.Yes return (\\(0 self : X.Choice) => String) of\n  X.Yes => "yes"\n  X.No => "no")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'yes\n')

    def test_formatter_round_trip(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('module Main\nimport A   as   X\nmain : IO Unit\nmain = putStrLn X.x\n')
            result = run_cli('format', str(path), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('import A as X', result.stdout)
            path.write_text(result.stdout)
            again = run_cli('format', str(path), timeout=120)
            self.assertEqual(again.stdout, result.stdout)

    def test_package_alias_and_dependency_ownership(self):
        import shutil
        fixtures = ROOT / 'examples/packages'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixtures / 'sum-library', root / 'sum-library')
            shutil.copytree(fixtures / 'sum-client', root / 'sum-client')
            app = root / 'sum-client'
            manifest = app / 'fibril.yaml'
            main = app / 'src/Main.fib'
            source = main.read_text().replace('import Data.Sum', 'import Data.Sum as S').replace('Data.Sum.', 'S.')
            main.write_text(source)
            result = run_cli('run', '--package', str(manifest), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'L: hello\nR: yes\n')
            bridge = root / 'bridge'
            (bridge / 'src').mkdir(parents=True)
            (bridge / 'fibril.yaml').write_text('schema: 1\nname: bridge\nmodule-prefix: Bridge\nsource-dir: src\nfoundation: de-morgan\ndependencies:\n  sum-library:\n    path: ../sum-library\n')
            manifest.write_text(manifest.read_text().replace('  sum-library:\n    path: ../sum-library', '  bridge:\n    path: ../bridge'))
            self.assertNotEqual(run_cli('check', '--package', str(manifest), timeout=120).returncode, 0)

    def test_named_provider_is_not_duplicated(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface C : Type where\n  constructor MkC\n  method : (1 text : String) -> String\nexport\nimplementation instance : C where\n  method = \\(1 text : String) => text\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A as X\nmain : IO Unit\nmain = putStrLn (X.method @{implementation} "ok")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'ok\n')

    def test_erased_export_stays_erased(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\n0 hidden : String\nhidden = "no"\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A as X\nmain : IO Unit\nmain = putStrLn X.hidden\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)

    def test_conflicts_malformed_and_transitive(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nx : String\nx = "a"\n')
            (root / 'B.fib').write_text('module B\nimport A\nexport\ny : String\ny = A.x\n')
            main = root / 'Main.fib'
            for imports in ['import A as X\nimport B as X', 'import A as B\nimport B', 'import A as Main', 'import A as A', 'import A as lower', 'import A as']:
                main.write_text('module Main\n' + imports + '\nmain : IO Unit\nmain = putStrLn "ok"\n')
                result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
                self.assertNotEqual(result.returncode, 0, imports)
            main.write_text('module Main\nimport B as X\nmain : IO Unit\nmain = putStrLn X.x\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)


class SelectiveImportTests(unittest.TestCase):
    def test_visibility_validation_and_navigation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nx : String\nx = "ok"\nexport\ny : String\ny = "no"\nsecret : String\nsecret = "private"\n')
            main = root / 'Main.fib'
            for reference in ['x', 'A.x', 'X.x']:
                main.write_text('module Main\nimport A as X (x)\nmain : IO Unit\nmain = putStrLn ' + reference + '\n')
                result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
                self.assertEqual(result.returncode, 0, result.stderr)
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '2', '16', str(main), timeout=120)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']).name, 'A.fib')
            for reference in ['y', 'A.y', 'X.y']:
                main.write_text('module Main\nimport A as X (x)\nmain : IO Unit\nmain = putStrLn ' + reference + '\n')
                self.assertNotEqual(run_cli('check', '--source-dir', directory, str(main), timeout=120).returncode, 0)
            for selection in ['secret', 'missing', 'x, x', '', 'x,', 'x y', 'A.x', 'x,\n y']:
                main.write_text('module Main\nimport A (' + selection + ')\nmain : IO Unit\nmain = putStrLn "ok"\n')
                self.assertNotEqual(run_cli('check', '--source-dir', directory, str(main), timeout=120).returncode, 0, selection)

    def test_ambiguity_and_provider_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nx : String\nx = "a"\nexport\ninterface C : Type where\n  constructor MkC\n  method : (1 text : String) -> String\nexport\nimplementation instance : C where\n  method = \\(1 text : String) => text\n')
            (root / 'B.fib').write_text('module B\nexport\nx : String\nx = "b"\nexport\ny : String\ny = "y"\n')
            main = root / 'Main.fib'
            def check(imports, expression):
                main.write_text('module Main\n' + imports + '\nmain : IO Unit\nmain = putStrLn ' + expression + '\n')
                return run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(check('import A (x)\nimport B (y)', 'x').returncode, 0)
            self.assertNotEqual(check('import A (x)\nimport B (x)', 'x').returncode, 0)
            self.assertEqual(check('import A (x)\nimport B (x)', 'A.x').returncode, 0)
            self.assertNotEqual(check('import A (method)', '(method @{implementation} "ok")').returncode, 0)
            self.assertEqual(check('import A (method, instance)', '(method @{implementation} "ok")').returncode, 0)

    def test_selective_constructor_patterns_and_erased_globals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ndata Choice {0 T : Type} : Type where\n  Present : (value : T) -> Choice T\n  Missing : Choice T\nexport\n0 hidden : String\nhidden = "private runtime"\n')
            main = root / 'Main.fib'
            source = ('module Main\nimport A as X (Choice, Present, Missing)\n'
                      'label : Choice String -> String\n'
                      'label x = case x return (\\(0 self : Choice String) => String) of\n'
                      '  Present value => value\n  Missing => "missing"\n'
                      'main : IO Unit\nmain = putStrLn (label (X.Present "ok"))\n')
            main.write_text(source)
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'ok\n')
            main.write_text(source.replace('Choice, Present, Missing', 'Choice, Present'))
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            main.write_text('module Main\nimport A (hidden)\nmain : IO Unit\nmain = putStrLn hidden\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)

    def test_selected_exports_across_package_boundary(self):
        import shutil
        fixtures = ROOT / 'examples/packages'
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(fixtures / 'sum-library', root / 'sum-library')
            shutil.copytree(fixtures / 'sum-client', root / 'sum-client')
            app = root / 'sum-client'
            main = app / 'src/Main.fib'
            original = main.read_text()
            source = original.replace('import Data.Sum', 'import Data.Sum as S (Sum, Left, Right)').replace('Data.Sum.', 'S.')
            main.write_text(source)
            result = run_cli('run', '--package', str(app / 'fibril.yaml'), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'L: hello\nR: yes\n')
            main.write_text(source.replace('(Sum, Left, Right)', '(Sum, Left)'))
            result = run_cli('check', '--package', str(app / 'fibril.yaml'), timeout=120)
            self.assertNotEqual(result.returncode, 0)

    def test_omitted_exports_do_not_shadow_prelude_or_leak_transitively(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nputStrLn : String -> IO Unit\nputStrLn x = pure Unit ()\nexport\nvalue : String\nvalue = "A"\n')
            (root / 'B.fib').write_text('module B\nimport A (value)\nexport\ntext : String\ntext = value\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport A (value)\nmain : IO Unit\nmain = putStrLn value\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'A\n')
            for reference in ['value', 'A.value']:
                main.write_text('module Main\nimport B (text)\nmain : IO Unit\nmain = putStrLn ' + reference + '\n')
                result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
                self.assertNotEqual(result.returncode, 0, reference)

    def test_interface_constructor_and_format(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface Ops (0 T : Type) : Type where\n  constructor MkOps\n  op : (x : T) -> T\n')
            main = root / 'Main.fib'
            body = 'implementation chosen : X.Ops String where\n  op = \\(x : String) => x\nmain : IO Unit\nmain = putStrLn "ok"\n'
            main.write_text('module Main\nimport A as X (Ops)\n' + body)
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('constructor', result.stderr + result.stdout)
            main.write_text('module Main\nimport A as X ( Ops , MkOps ) -- comment\n' + body)
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            formatted = run_cli('format', str(main), timeout=120)
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn('import A as X (Ops, MkOps)', formatted.stdout)
            main.write_text(formatted.stdout)
            self.assertEqual(run_cli('format', str(main), timeout=120).stdout, formatted.stdout)


class LibraryPackageDefinitionTests(unittest.TestCase):
    def test_inventory_navigation_and_checked_boundaries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            a = root / 'a'
            b = root / 'b'
            (a / 'src/A').mkdir(parents=True)
            (b / 'src/B').mkdir(parents=True)
            (a / 'fibril.yaml').write_text('schema: 1\nname: a\nmodule-prefix: A\nsource-dir: src\nfoundation: de-morgan\nmodules: [A.Value]\ndependencies: {}\n')
            (b / 'fibril.yaml').write_text('schema: 1\nname: b\nmodule-prefix: B\nsource-dir: src\nfoundation: de-morgan\nmodules: [B.Facade]\ndependencies:\n  a:\n    path: ../a\n')
            original = a / 'src/A/Value.fib'
            facade = b / 'src/B/Facade.fib'
            original.write_text('module A.Value\nexport\nx : String\nx = "ok"\nsecret : String\nsecret = "private"\n')
            facade.write_text('module B.Facade\nimport public A.Value as V (x)\nexport\ny : String\ny = x\n')
            result = run_cli('definition', '--package', str(b / 'fibril.yaml'), '5', '5', str(facade), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            packet = json.loads(result.stdout)
            self.assertEqual(packet['entry'], '')
            self.assertEqual(Path(packet['manifest']), (b / 'fibril.yaml').resolve())
            self.assertEqual(Path(packet['definition']['path']), original.resolve())
            self.assertEqual({Path(item['path']) for item in packet['sources']}, {original.resolve(), facade.resolve()})
            selector = facade.read_text().splitlines()[1].rfind('x') + 1
            result = run_cli('definition', '--package', str(b / 'fibril.yaml'), '2', str(selector), str(facade), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']), original.resolve())
            source = facade.read_text()
            facade.write_text('module B.Facade\nimport A.Value (x)\nx : String\nx = "local"\nexport\ny : String\ny = x\n')
            result = run_cli('definition', '--package', str(b / 'fibril.yaml'), '7', '5', str(facade), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            local = json.loads(result.stdout)['definition']
            self.assertEqual(Path(local['path']), facade.resolve())
            self.assertEqual(local['range']['start']['line'], 4)
            facade.write_text('module B.Facade\nimport A.Value (x)\nexport\ny : String\ny = later\nlater : String\nlater = x\n')
            result = run_cli('definition', '--package', str(b / 'fibril.yaml'), '5', '5', str(facade), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            facade.write_text(source)
            manifest = b / 'fibril.yaml'
            saved_manifest = manifest.read_text()
            manifest.write_text('schema: invalid\n')
            result = run_cli('definition', '--package', str(manifest), '5', '5', str(facade), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            manifest.write_text(saved_manifest.replace('    path: ../a', '    path: ../missing'))
            result = run_cli('definition', '--package', str(manifest), '5', '5', str(facade), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            manifest.write_text(saved_manifest)
            facade.write_text(source.replace('y = x', 'y = V.secret'))
            result = run_cli('definition', '--package', str(b / 'fibril.yaml'), '5', '7', str(facade), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')


class PublicImportTests(unittest.TestCase):
    def test_public_visibility_diamonds_collisions_and_syntax(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\nx : String\nx = "ok"\nexport\ny : String\ny = "hidden"\nsecret : String\nsecret = "private"\n')
            (root / 'B.fib').write_text('module B\nimport public A as X (x)\n')
            (root / 'C.fib').write_text('module C\nimport public A (x)\n')
            main = root / 'Main.fib'
            def check(imports, expr):
                main.write_text('module Main\n' + imports + '\nmain : IO Unit\nmain = putStrLn ' + expr + '\n')
                return run_cli('check', '--source-dir', directory, str(main), timeout=120)
            for ref in ['x', 'B.x', 'C.x', 'Z.x']:
                result = check('import B as Z\nimport C', ref)
                self.assertEqual(result.returncode, 0, result.stderr)
            for ref in ['A.x', 'y', 'B.y', 'secret']:
                self.assertNotEqual(check('import B', ref).returncode, 0, ref)
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '2', '8', str(main), timeout=120)
            # A failed project does not provide checked navigation.
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(check('import B', 'B.x').returncode, 0)
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '4', '19', str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']).name, 'A.fib')
            for ref in ['x', 'B.x', 'C.x', 'Z.x']:
                self.assertEqual(check('import B as Z\nimport C', ref).returncode, 0)
                line = main.read_text().splitlines()[4]
                column = line.rfind(ref) + len(ref)
                result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '5', str(column), str(main), timeout=120)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(Path(json.loads(result.stdout)['definition']['path']).name, 'A.fib', ref)
            self.assertEqual(check('import B (x)', 'x').returncode, 0)
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '2', '11', str(main), timeout=120)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']).name, 'A.fib')
            result = run_cli('definition', '--source-dir', directory, '--entry', str(main), '2', '23', str(root / 'B.fib'), timeout=120)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']).name, 'A.fib')
            for selection in ['secret', 'missing']:
                (root / 'B.fib').write_text('module B\nimport public A (' + selection + ')\n')
                self.assertNotEqual(check('import B', '"ok"').returncode, 0)
            for header in ['import public A', 'import public A ()', 'import public A (x) as X']:
                (root / 'B.fib').write_text('module B\n' + header + '\n')
                self.assertNotEqual(check('import B', '"ok"').returncode, 0, header)
            (root / 'B.fib').write_text('module B\nimport public A (x)\nexport\nx : String\nx = "local"\n')
            self.assertNotEqual(check('import B', '"ok"').returncode, 0)
            (root / 'D.fib').write_text('module D\nexport\nx : String\nx = "other"\n')
            (root / 'B.fib').write_text('module B\nimport public A (x)\nimport public D (x)\n')
            self.assertNotEqual(check('import B', '"ok"').returncode, 0)
            (root / 'B.fib').write_text('module B\nimport public A as X ( x )\n')
            formatted = run_cli('format', str(root / 'B.fib'), timeout=120)
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            self.assertIn('import public A as X (x)', formatted.stdout)

    def test_erased_provider_interfaces_and_patterns(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\n0 hidden : String\nhidden = "no"\nexport\ninterface C : Type where\n  constructor MkC\n  method : (1 text : String) -> String\nexport\nimplementation instance : C where\n  method = \\(1 text : String) => text\nexport\ndata Choice : Type where\n  Yes : Choice\n  No : Choice\n')
            facade = root / 'B.fib'
            main = root / 'Main.fib'
            facade.write_text('module B\nimport public A (hidden, method, instance, Choice, Yes, No)\n')
            main.write_text('module Main\nimport B\nmain : IO Unit\nmain = putStrLn (method @{implementation} "ok")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'ok\n')
            main.write_text('module Main\nimport B\nmain : IO Unit\nmain = putStrLn hidden\n')
            self.assertNotEqual(run_cli('check', '--source-dir', directory, str(main), timeout=120).returncode, 0)
            main.write_text('module Main\nimport B\nmain : IO Unit\nmain = putStrLn (case B.Yes return (\\(0 self : B.Choice) => String) of\n  B.Yes => "yes"\n  B.No => "no")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            main.write_text('module Main\nimport B\nmain : IO Unit\nmain = putStrLn "independent"\n')
            for selection in ['C', 'MkC', 'C, MkC']:
                facade.write_text('module B\nimport public A (' + selection + ')\n')
                result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_public_interface_constructors_require_matching_origin(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface C : Type where\n  constructor MkC\n  method : (text : String) -> String\n')
            (root / 'D.fib').write_text('module D\nexport\ninterface Other : Type where\n  constructor MkC\n  method : (text : String) -> String\n')
            facade = root / 'B.fib'
            main = root / 'Main.fib'
            main.write_text('module Main\nimport B\nimplementation chosen : B.C where\n  method = \\(text : String) => text\nmain : IO Unit\nmain = putStrLn "ok"\n')
            for imports in ['import public A (C)', 'import public A (C)\nimport public D (MkC)']:
                facade.write_text('module B\n' + imports + '\n')
                result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
                self.assertNotEqual(result.returncode, 0, imports)
                self.assertIn('constructor', result.stderr)
            facade.write_text('module B\nimport public A (C, MkC)\n')
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            selected = main.read_text().replace('import B', 'import B (C)')
            main.write_text(selected)
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('constructor', result.stderr)
            main.write_text(selected.replace('import B (C)', 'import B (C, MkC)'))
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            (root / 'E.fib').write_text('module E\nimport public B (C, MkC)\n')
            main.write_text(main.read_text().replace('import B (C, MkC)', 'import E').replace('B.C', 'E.C'))
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_public_interface_constructor_across_paths_is_order_independent(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface C : Type where\n  constructor MkC\n  method : (text : String) -> String\n')
            (root / 'B.fib').write_text('module B\nimport public A (C)\n')
            (root / 'D.fib').write_text('module D\nimport public A (C, MkC)\n')
            (root / 'E.fib').write_text('module E\nimport public A (MkC)\n')
            main = root / 'Main.fib'
            body = 'implementation chosen : C where\n  method = \\(text : String) => text\nmain : IO Unit\nmain = putStrLn "ok"\n'
            for imports in ['import B\nimport D', 'import D\nimport B', 'import B\nimport E', 'import E\nimport B']:
                main.write_text('module Main\n' + imports + '\n' + body)
                result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
                self.assertEqual(result.returncode, 0, imports + '\n' + result.stderr)
            main.write_text('module Main\nimport B\n' + body)
            result = run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('constructor', result.stderr)

    def test_public_interface_diamond_with_unique_provider(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'A.fib').write_text('module A\nexport\ninterface C : Type where\n  constructor MkC\n  method : (1 text : String) -> String\nexport\nimplementation instance : C where\n  method = \\(1 text : String) => text\n')
            for name in ['B', 'D']:
                (root / (name + '.fib')).write_text('module ' + name + '\nimport public A (C, MkC, method, instance)\n')
            main = root / 'Main.fib'
            main.write_text('module Main\nimport B\nimport D\nmain : IO Unit\nmain = putStrLn (method @{implementation} "ok")\n')
            result = run_cli('run', '--source-dir', directory, str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, 'ok\n')

    def test_distinct_origins_own_main_changes_and_cycles(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            a = root / 'A.fib'
            b = root / 'B.fib'
            c = root / 'C.fib'
            main = root / 'Main.fib'
            a.write_text('module A\nexport\nx : String\nx = "a"\nexport\nmain : IO Unit\nmain = putStrLn "a"\n')
            b.write_text('module B\nimport public A (x, main)\n')
            c.write_text('module C\nexport\nx : String\nx = "c"\n')
            def check(source):
                main.write_text(source)
                return run_cli('check', '--source-dir', directory, str(main), timeout=120)
            self.assertNotEqual(check('module Main\nimport B\n').returncode, 0)
            self.assertNotEqual(check('module Main\nimport B\nimport C\nmain : IO Unit\nmain = putStrLn x\n').returncode, 0)
            result = check('module Main\nimport B\nimport C\nmain : IO Unit\nmain = putStrLn B.x\n')
            self.assertEqual(result.returncode, 0, result.stderr)
            a.write_text(a.read_text().replace('export\nx : String', 'x : String'))
            self.assertNotEqual(check('module Main\nimport B\nmain : IO Unit\nmain = putStrLn "ok"\n').returncode, 0)
            a.write_text('module A\nimport B\nexport\nx : String\nx = "a"\n')
            self.assertNotEqual(check('module Main\nimport B\nmain : IO Unit\nmain = putStrLn "ok"\n').returncode, 0)
            main.write_text('import public A (x)\nmain : IO Unit\nmain = putStrLn "ok"\n')
            self.assertNotEqual(run_cli('check', '--source-dir', directory, str(main), timeout=120).returncode, 0)

    def test_package_public_import_permissions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def package(name, prefix, deps, entry=False):
                folder = root / name
                (folder / 'src').mkdir(parents=True)
                (folder / 'fibril.yaml').write_text(f'schema: 1\nname: {name}\nmodule-prefix: {prefix}\nsource-dir: src\nfoundation: de-morgan\n' + ('entry: Main\n' if entry else '') + 'dependencies:\n' + (''.join(f'  {key}:\n    path: ../{key}\n' for key in deps) if deps else '  {}\n'))
                return folder
            core = package('core', 'Core', [])
            bridge = package('bridge', 'Bridge', ['core'])
            app = package('app', 'App', ['bridge'], True)
            (core / 'src/Core').mkdir()
            (bridge / 'src/Bridge').mkdir()
            (core / 'src/Core/Text.fib').write_text('module Core.Text\nexport\nx : String\nx = "ok"\nexport\ny : String\ny = "not selected"\nsecret : String\nsecret = "private"\n')
            (bridge / 'src/Bridge/Facade.fib').write_text('module Bridge.Facade\nimport public Core.Text (x)\n')
            main = app / 'src/Main.fib'
            main.write_text('module Main\nimport Bridge.Facade\nmain : IO Unit\nmain = putStrLn Bridge.Facade.x\n')
            result = run_cli('run', '--package', str(app / 'fibril.yaml'), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            manifest_path = str(app / 'fibril.yaml')
            for reference in ['Bridge.Facade.x', 'x', 'F.x']:
                main.write_text('module Main\nimport Bridge.Facade as F\nmain : IO Unit\nmain = putStrLn ' + reference + '\n')
                column = main.read_text().splitlines()[3].rfind(reference) + len(reference)
                result = run_cli('definition', '--package', manifest_path, '4', str(column), str(main), timeout=120)
                self.assertEqual(result.returncode, 0, result.stderr)
                packet = json.loads(result.stdout)
                self.assertEqual(packet['version'], 2)
                self.assertEqual(Path(packet['definition']['path']), (core / 'src/Core/Text.fib').resolve())
                snapshots = {Path(item['path']): item['text'] for item in packet['sources']}
                self.assertEqual(snapshots[main.resolve()], main.read_text())
                self.assertEqual(snapshots[(core / 'src/Core/Text.fib').resolve()], (core / 'src/Core/Text.fib').read_text())
            result = run_cli('definition', '--package', 'app/fibril.yaml', '4', '5', 'app/src/../src/Main.fib', cwd=root, timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIsNone(json.loads(result.stdout)['definition'])
            for reference in ['F.y', 'F.secret']:
                main.write_text('module Main\nimport Bridge.Facade as F\nmain : IO Unit\nmain = putStrLn ' + reference + '\n')
                result = run_cli('definition', '--package', manifest_path, '4', '19', str(main), timeout=120)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')
            (bridge / 'src/Bridge/Other.fib').write_text('module Bridge.Other\nexport\nx : String\nx = "distinct"\n')
            main.write_text('module Main\nimport Bridge.Facade\nimport Bridge.Other\nmain : IO Unit\nmain = putStrLn x\n')
            result = run_cli('definition', '--package', manifest_path, '5', '18', str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            (bridge / 'src/Bridge/Twin.fib').write_text('module Bridge.Twin\nimport public Core.Text (x)\n')
            main.write_text('module Main\nimport Bridge.Facade\nimport Bridge.Twin\nmain : IO Unit\nmain = putStrLn x\n')
            result = run_cli('definition', '--package', manifest_path, '5', '17', str(main), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']), (core / 'src/Core/Text.fib').resolve())
            main.write_text('module Main\nimport Bridge.Facade as F\nmain : IO Unit\nmain = putStrLn F.x\n')
            facade = bridge / 'src/Bridge/Facade.fib'
            selector = facade.read_text().splitlines()[1].rfind('x') + 1
            result = run_cli('definition', '--package', manifest_path, '2', str(selector), str(facade), timeout=120)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(json.loads(result.stdout)['definition']['path']), (core / 'src/Core/Text.fib').resolve())
            outside = root / 'Outside.fib'
            outside.write_text('module Outside\n')
            result = run_cli('definition', '--package', manifest_path, '1', '1', str(outside), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('not in the checked project graph', result.stderr)
            main.write_text(main.read_text().replace('import Bridge.Facade as F', 'import Bridge.Facade as F\nimport Core.Text'))
            self.assertNotEqual(run_cli('check', '--package', str(app / 'fibril.yaml'), timeout=120).returncode, 0)
            result = run_cli('definition', '--package', manifest_path, '5', '19', str(main), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            main.write_text(main.read_text().replace('\nimport Core.Text', ''))
            manifest = bridge / 'fibril.yaml'
            manifest.write_text(manifest.read_text().replace('  core:\n    path: ../core\n', '  {}\n'))
            self.assertNotEqual(run_cli('check', '--package', str(app / 'fibril.yaml'), timeout=120).returncode, 0)


class IndexedDataTests(unittest.TestCase):
    @staticmethod
    def fixture():
        return (ROOT / 'examples/modules/indexed-vect/Main.fib').read_text()

    def check_source(self, source, accepted, diagnostic=None):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            result = run_cli('check', '--source-dir', directory, str(path), timeout=120)
        if accepted:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            if diagnostic:
                self.assertIn(diagnostic, result.stdout + result.stderr)

    def test_indexed_vectors_run_and_format(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(self.fixture())
            formatted = run_cli('format', str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run_cli('format', '--check', str(path)).returncode, 0)
            result = run_cli('run', '--source-dir', directory, '--fuel', '4096', str(path), timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'first\n!!!!\n')

    def test_indexed_vectors_refuse_wrong_constructor_indices(self):
        source = self.fixture()
        for before, after in [('Nil : Vect A Zero', 'Nil : Vect A True'),
                              ('Nil : Vect A Zero', 'Nil : Vect A'),
                              ('Vect String (Succ (Succ Zero))', 'Vect String Zero'),
                              ('(rest : Vect A n)', '(rest : Vect String n)')]:
            with self.subTest(after=after):
                self.check_source(source.replace(before, after), False)

    def test_indexed_vectors_allow_implicit_constructor_parameters(self):
        source = self.fixture().replace('data Vect (0 A : Type)', 'data Vect {0 A : Type}')
        for constructor in ['Nil', 'Cons']:
            for argument in ['A', 'String']:
                source = source.replace(constructor + ' ' + argument, constructor + ' {' + argument + '}')
        self.check_source(source, True)

    def test_indexed_vectors_refuse_negative_recursion(self):
        self.check_source(self.fixture().replace('(rest : Vect A n)',
                          '(rest : (ignored : Nat) -> Vect A n)'), False, 'function type')

    def test_indexed_vectors_require_erased_indices(self):
        self.check_source(self.fixture().replace('(0 length : Nat)', '(length : Nat)'), False, 'explicit 0')

    def test_indexed_vectors_refuse_bad_motives_and_incomplete_coverage(self):
        source = self.fixture()
        for before, after in [
            ('return (\\(0 k : Nat) => \\(0 self : Vect A k) => Vect A k)', ''),
            ('\\(0 k : Nat) => \\(0 self : Vect A k) => Vect A k', '\\(0 self : Vect A n) => Vect A n'),
            ('  Nil => Zero\n', '')]:
            with self.subTest(after=after):
                self.assertIn(before, source)
                self.check_source(source.replace(before, after), False)

    def test_indexed_vectors_refuse_nondecreasing_recursion(self):
        self.check_source(self.fixture().replace('Succ (length A k rest)', 'Succ (length A n xs)'), False)

    def test_indexed_vectors_cannot_observe_erased_constructor_index(self):
        self.check_source(self.fixture().replace('Succ (length A k rest)', 'k'), False, 'usage')

    def test_indexed_nonrecursive_family_and_dependent_indices(self):
        source = '''module Main
data Pick (0 A : Type) : (0 value : A) -> (0 enabled : Bool) -> Type where
  Selected : (value : A) -> Pick A value True
sample : Pick String "chosen" True
sample = Selected String "chosen"
main : IO Unit
main = case sample of
  Selected value => putStrLn value
'''
        self.check_source(source, True)
        self.check_source(source.replace('Pick String "chosen" True', 'Pick String "other" True'), False)
        self.check_source(source.replace('Pick String "chosen" True', 'Pick String "chosen" False'), False)
        self.check_source(source.replace('case sample of',
            'case sample return (\\(0 value : String) => \\(0 enabled : Bool) => '
            '\\(0 self : Pick String value enabled) => IO Unit) of'), True)

    def test_indexed_family_later_index_depends_on_earlier_index(self):
        source = self.fixture().split('main : IO Unit')[0] + '''data Packed : (0 n : Nat) -> (0 xs : Vect String n) -> Type where
  Pack : (0 n : Nat) -> (0 xs : Vect String n) -> Packed n xs
packed : Packed (Succ (Succ Zero)) sample
packed = Pack (Succ (Succ Zero)) sample
main : IO Unit
main = case packed of
  Pack n xs => putStrLn "packed"
'''
        self.check_source(source, True)
        self.check_source(source.replace('packed : Packed (Succ (Succ Zero)) sample',
                                         'packed : Packed Zero sample'), False)

    def test_indexed_vectors_preserve_linear_ownership(self):
        source = '''module Main
data Vect (0 A : Type) : (0 n : Nat) -> Type where
  Nil : Vect A Zero
  Cons : (0 n : Nat) -> (1 value : A) -> (1 rest : Vect A n) -> Vect A (Succ n)
drain : (0 n : Nat) -> (1 xs : Vect String n) -> String
drain n xs = case xs of
  Nil => ""
  Cons k value rest => appendString value (drain k rest)
main : IO Unit
main = putStrLn (drain (Succ Zero) (Cons String Zero "linear" (Nil String)))
'''
        self.check_source(source, True)
        self.check_source(source.replace('appendString value (drain k rest)',
                          'appendString value (appendString value (drain k rest))'), False, 'usage')
        self.check_source(source.replace('appendString value (drain k rest)', 'value'), False, 'usage')

    def test_indexed_vectors_import_with_qualified_constructors(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Vectors.fib').write_text(self.fixture().replace('module Main', 'module Vectors', 1)
                                               .replace('data Vect', 'export\ndata Vect', 1))
            path = root / 'Main.fib'
            path.write_text('module Main\nimport Vectors as V\n'
                'sample : V.Vect String Zero\nsample = V.Nil String\n'
                'main : IO Unit\nmain = case sample of\n'
                '  V.Nil => putStrLn "imported"\n  V.Cons k value rest => putStrLn "nonempty"\n')
            result = run_cli('run', '--source-dir', directory, str(path), timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'imported\n')


if __name__ == "__main__":
    unittest.main()
