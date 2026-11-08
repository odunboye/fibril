#!/usr/bin/env python3
"""Source-only 64-byte diagnostic adoption; budget blockers are NOT matches.

Private package staging and observer copies only. No runtime limits are changed.
Python JSON is the reference oracle, never the executing parser.
"""
import ast
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile
import unittest

from test_units import prepare_environment

from observe_json_state_sharing import cases, oracle, check_source_preservation
from test_binary_iteration import observe

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'tools/fixtures/json-iteration'
EXE = Path(os.environ.get('FIBRIL', ROOT / 'build/exec/fibril'))


def checked(command, **kwargs):
    result = subprocess.run(list(map(str, command)), capture_output=True, timeout=120, **kwargs)
    if result.returncode:
        raise AssertionError((command, result.returncode, result.stdout, result.stderr))
    return result


def matrix():
    yield from cases()
    yield from [('duplicate-invalid-first', b'{"a":"\\ud800","a":0}'),
                ('duplicate-invalid-last', b'{"a":0,"a":"\\ud800"}'),
                ('duplicate-invalid-nested', b'{"a":{"x":"\\ud800"},"a":0}'),
                ('raw-nul', b'"\0"'), ('escaped-nul', b'"\\u0000"'),
                ('all-short-escapes', b'"\\\"\\\\\\/\\b\\f\\n\\r\\t"'),
                ('number-exact', b'-0.1200E+02'), ('negative-zero', b'-0'),
                ('noncharacter-escape', b'"\\uffff"'),
                ('noncharacter-raw', '"\uffff"'.encode()),
                ('noncharacter-pair', b'"\\uDBFF\\uDFFF"'),
                ('utf8-overlong-four', b'"\xf0\x80\x80\x80"'),
                ('utf8-too-large', b'"\xf4\x90\x80\x80"'),
                ('utf8-truncated', b'"\xe2\x82"'),
                ('raw-control-31', b'"\x1f"'),
                ('array-required-value', b'[0,]'), ('object-required-key', b'{"a":0,}'),
                ('members-10', b'{' + b','.join([b'"a":0'] * 10) + b'}'),
                ('tokens-64', b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']'),
                ('tokens-65-byte-denial', b'[' + b','.join([b'0'] * 32) + b']'),
                ('string-bytes-64', b'"' + b'a' * 62 + b'"'),
                ('number-bytes-64', b'1' * 64),
                ('string-high-utf8-64', ('"' + 'ÿ' * 31 + '"').encode()),
                ('string-four-byte-utf8-62', ('"' + '😀' * 15 + '"').encode()),
                ('trailing-invalid-64', b'0' + b' ' * 62 + b'x'),
                ('early-invalid-64', b'x' + b' ' * 63)]


class JSONIteration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='fibril-json-iteration-')
        cls.work = Path(cls.temporary.name)
        cls.rows = []
        env = prepare_environment()
        compiler = shlex.split(env.get('IDRIS2', str(ROOT / 'tools/fibril_idris.py')))
        # Exact observer insertion, no rewritten evaluator decisions or budgets.
        driver = (ROOT / 'src/Fibril/Driver/Binary.idr').read_text()
        needle = '        response <- executeGlobals globals depth fuel transport (Apply step ready)'
        assert driver.count(needle) == 1
        driver = driver.replace('module Fibril.Driver.Binary\n', 'module ObservedBinaryDriver\n', 1)
        driver = driver.replace(needle, '        putStrLn "CALLBACK"\n' + needle)
        (cls.work / 'ObservedBinaryDriver.idr').write_text(driver)
        shutil.copyfile(FIXTURE / 'Hosted.idr', cls.work / 'Hosted.idr')
        (cls.work / 'hosted.ipkg').write_text('package json-iteration-hosted\nsourcedir = "."\ndepends = fibril, yaml\nmodules = ObservedBinaryDriver, Hosted\nmain = Hosted\nexecutable = hosted\n')
        checked(compiler + ['--build', 'hosted.ipkg'], cwd=cls.work, env=env)
        shutil.copyfile(ROOT / 'tools/fixtures/json-admission/Measure.idr', cls.work / 'Measure.idr')
        (cls.work / 'measure.ipkg').write_text('package json-iteration-measure\nsourcedir = "."\ndepends = fibril, yaml\nmain = Measure\nexecutable = measure\n')
        checked(compiler + ['--build', 'measure.ipkg'], cwd=cls.work, env=env)
        cls.measure = cls.work / 'build/exec/measure'
        cls.hosted = cls.work / 'build/exec/hosted'
        cls.cc = shlex.split(env.get('CC', 'cc'))
        cls.counter = 0
        cls.reader = cls.source((FIXTURE / 'Read65.fib').read_text())

    @classmethod
    def tearDownClass(cls):
        output = os.environ.get('JSON_ITERATION_EVIDENCE')
        if output:
            Path(output).write_text(json.dumps({'scope': '64-byte diagnostic, not 4096-byte delivery', 'rows': cls.rows}, indent=2) + '\n')
        cls.temporary.cleanup()

    @classmethod
    def source(cls, entry, module=None):
        cls.counter += 1
        work = cls.work / str(cls.counter)
        (work / 'Protocol').mkdir(parents=True)
        (work / 'Protocol/JSON.fib').write_text(module or (FIXTURE / 'Protocol/JSON.fib').read_text())
        (work / 'Main.fib').write_text(re.sub(r'^module \w+', 'module Main', entry))
        checked([EXE, 'check', '--source-dir', work, work / 'Main.fib'])
        emitted = checked([EXE, 'emit-c-binary', '--source-dir', work, work / 'Main.fib'])
        (work / 'program.c').write_bytes(emitted.stdout)
        observe(work)
        assert (work / 'fibril_binary_runtime.c').read_text().count('(iteration_callbacks++, apply_thunk(r, step, input))') == 2
        shutil.copyfile(FIXTURE / 'SourceHarness.c', work / 'harness.c')
        checked(cls.cc + ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-I', work, work / 'harness.c', '-o', work / 'native'])
        return work

    def both(self, source, label, data):
        rows = []
        for backend, command in [('hosted', [self.hosted, source, source / 'Main.fib', data.hex()]),
                                 ('native', [source / 'native', data.hex()])]:
            result = checked(command)
            self.assertEqual(result.stderr, b'')  # includes sanitizer diagnostics
            text = result.stdout.decode()
            output = bytes(ast.literal_eval(re.search(r'^OUTPUT (.*)$', text, re.M)[1]))
            metrics = list(map(int, re.search(r'^METRICS ([\d ]+)$', text, re.M)[1].split()))
            error = re.search(r'^ERROR (.*)$', text, re.M)
            native = re.search(r'^NATIVE ([\d ]+)$', text, re.M)
            callbacks = int(native[1].split()[-1]) if native else text.count('CALLBACK\n')
            expected = oracle(data)[2]
            category = 'invalid_json' if output == b'\0' else 'valid_transfer'
            if error:
                self.assertEqual(output, b'')
                if 'budget exhausted' in error[1] or 'depth exhausted' in error[1]:
                    category = 'budget_rejection'
                elif not data and error[1] == 'Binary program rejected input':
                    category = 'reader_eof'
                else:
                    self.fail(text)
            else:
                self.assertIn('\nOK\n', text)
                self.assertEqual(output, expected, (label, backend, text))
            row = dict(case=label, backend=backend, input_hex=data.hex(), expected_hex=expected.hex(),
                       stdout_hex=output.hex(), category=category, callbacks=callbacks, metrics=metrics,
                       observation=text.strip())
            self.rows.append(row)
            rows.append(row)
            print('JSON_ITERATION_ROW ' + json.dumps(row), flush=True)
        return rows

    def test_real_checked_binary_stdio_named_subset(self):
        for data in (b'[1]', b'{"a":1,"a":2}', b'"\\uD834\\uDD1E"', b'"\0"', b' ' * 63 + b'1'):
            for command in ([EXE, 'run-binary', '--source-dir', self.reader, self.reader / 'Main.fib'], [self.reader / 'native']):
                result = checked(command, input=data)
                self.assertEqual(result.stderr, b'')
                self.assertEqual(result.stdout, oracle(data)[2])

    def test_api_and_clients_fit_unchanged_admission(self):
        for name in ('Parse.fib', 'ParseBinary.fib', 'PureRead65.fib', 'Read65.fib'):
            result = checked([self.measure, FIXTURE, FIXTURE / name])
            match = re.fullmatch(rb'CORE_NODES=(\d+) PAYLOAD=(\d+)\n', result.stdout)
            self.assertIsNotNone(match, result.stdout)
            nodes, payload = map(int, match.groups())
            self.assertLessEqual(nodes, 8192)
            self.assertLessEqual(payload, 16777216)
            self.rows.append(dict(case='admission-' + name, core_nodes=nodes, literal_payload=payload))

    def test_source_transition_and_finalizer_preservation(self):
        check_source_preservation()
        original = (ROOT / 'tools/fixtures/json-admission/shared/Protocol/JSON.fib').read_text()
        current = (FIXTURE / 'Protocol/JSON.fib').read_text()
        old = original.split('parseJSONKernel S scanning eliminate input = ', 1)[1]
        new = current.split('parseJSONKernel S scanning eliminate A run invalid input = ', 1)[1]
        self.assertEqual(old.split('  if primBytesLengthIs one', 1)[0], new.split('  let (finish :', 1)[0])
        finalizer = old.split('      (\\(rest : Bytes)', 1)[1].split('\n-- Instantiate', 1)[0][:-3]
        self.assertEqual(finalizer, new.split('      (\\(rest : Bytes)', 1)[1].split(') in\n', 1)[0])
        for forbidden in ('primReadBytes', 'primWriteBytes', 'primFlushBytes', 'primRejectBytes'):
            self.assertNotIn(forbidden, current)
        self.assertEqual(current.count('let (step :'), 1)
        self.assertIn('finish (natRec', current)

    def test_all_prior_cases_and_extended_boundaries(self):
        totals = {b: {} for b in ('hosted', 'native')}
        for label, data in matrix():
            with self.subTest(case=label):
                for row in self.both(self.reader, label, data):
                    self.assertNotEqual(row['category'], 'budget_rejection', (label, row['backend']))
                    counts = totals[row['backend']]
                    counts[row['category']] = counts.get(row['category'], 0) + 1
                    self.assertEqual(row['metrics'][:3], [1, int(row['category'] in ('valid_transfer', 'invalid_json')), int(row['category'] in ('valid_transfer', 'invalid_json'))])
                    if row['category'] == 'valid_transfer':
                        self.assertEqual(row['callbacks'], len(data) + 1)
                    if row['category'] in ('valid_transfer', 'invalid_json'):
                        self.assertLessEqual(row['callbacks'], len(data) + 1)
                    if label == 'early-invalid-64':
                        self.assertEqual(row['callbacks'], 2)
        print('JSON_ITERATION_SUMMARY ' + json.dumps(totals), flush=True)

    def test_empty_input_direct_and_exhaustion_are_data(self):
        entry = '''module Main
import Protocol.JSON
main : IO Unit
main = primBind JSONResult Unit (parseJSONBinary primBytesEmpty) (\\(1 result : JSONResult) => case result of
  InvalidJSON => primWriteBytes (primBytesOctetMod256 Zero)
  JSONTokens tokens => primWriteBytes tokens
  JSONBoundedFailure => primWriteBytes (primBytesOctetMod256 (Succ Zero)))
'''
        source = self.source(entry)
        for row in self.both(source, 'direct-empty', b''):
            self.assertEqual(row['category'], 'invalid_json')
            self.assertEqual(row['metrics'], [0, 1, 1, 0, 1])
            self.assertEqual(row['callbacks'], 1)
        # Checked private negative controls force Exhausted with unconsumed state.
        module = (FIXTURE / 'Protocol/JSON.fib').read_text()
        for count, expected_callbacks in [('Zero', 0), ('Succ Zero', 1)]:
            altered = module.replace('(Succ count) next initial', '(' + count + ') next initial')
            self.assertNotEqual(altered, module)
            source = self.source((FIXTURE / 'Read65.fib').read_text(), altered)
            for backend, command in [('hosted', [self.hosted, source, source / 'Main.fib', '5b315d']), ('native', [source / 'native', '5b315d'])]:
                result = checked(command)
                text = result.stdout.decode()
                self.assertEqual(result.stderr, b'')
                self.assertIn('OUTPUT [1]\nOK\n', text)
                self.assertIn('METRICS 1 1 1 0 1', text)
                callbacks = int(re.search(r'^NATIVE .* (\d+)$', text, re.M)[1]) if backend == 'native' else text.count('CALLBACK\n')
                self.assertEqual(callbacks, expected_callbacks)
                self.rows.append(dict(case='exhaustion-' + count, backend=backend, observation=text.strip()))

    def test_control_classifier_cost_diagnostic_only(self):
        module = (FIXTURE / 'Protocol/JSON.fib').read_text()
        needle = next(line for line in module.splitlines() if line.startswith('  let (control :'))
        altered = module.replace(needle, '  let (control : (b : Bytes) -> Bool) = \\(b : Bytes) => False in')
        source = self.source((FIXTURE / 'Read65.fib').read_text(), altered)
        # This is NOT a parser alternative: control validation is deliberately
        # bypassed solely to measure its cost on already-valid ASCII input.
        for row in self.both(source, 'diagnostic-control-bypass-string64', b'"' + b'a' * 62 + b'"'):
            self.assertEqual(row['category'], 'valid_transfer')

    def test_no_parser_transport_and_existing_mode_gates(self):
        entry = '''module Main
import Protocol.JSON
main : IO Unit
main = primBind JSONResult Unit (parseJSONBinary (primUTF8Case Bytes Bytes (primUTF8Encode "[1]") primBytesEmpty (\\(1 bytes : Bytes) => bytes))) (\\(1 result : JSONResult) => case result of
  InvalidJSON => primPure Unit ()
  JSONTokens tokens => if primBytesLengthIs Zero tokens then primPure Unit () else primPure Unit ()
  JSONBoundedFailure => primPure Unit ())
'''
        source = self.source(entry)
        for command in ([self.hosted, source, source / 'Main.fib', ''], [source / 'native', '']):
            result = checked(command)
            self.assertEqual(result.stderr, b'')
            text = result.stdout.decode()
            self.assertIn('METRICS 0 0 1 0 0\nOUTPUT []\nOK\n', text)
            callbacks = int(re.search(r'^NATIVE .* (\d+)$', text, re.M)[1]) if command[0] != self.hosted else text.count('CALLBACK\n')
            self.assertEqual(callbacks, 4)
            self.rows.append(dict(case='no-parser-transport', observation=text.strip()))
        # Interactive/resource admission is exercised on the actual checked term
        # by Hosted.idr (their CLI runners do not support module graphs).
        for mode in ('run', 'emit-c'):
            result = subprocess.run(list(map(str, [EXE, mode, '--source-dir', source, source / 'Main.fib'])), capture_output=True, timeout=30)
            self.assertNotEqual(result.returncode, 0, mode)
            self.assertEqual(result.stdout, b'', mode)
            self.assertNotIn(b'Unsupported command', result.stdout + result.stderr, mode)
            self.assertTrue(result.stderr, mode)


if __name__ == '__main__':
    unittest.main()
