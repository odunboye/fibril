#!/usr/bin/env python3
"""Typed-event SOURCE-ONLY prototype. No wire decoder or transport input.

Python supplies typed source fixtures and a finite transition-table oracle;
execution is the actual checked Fibril term on hosted and emitted-native runners.
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

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'tools/fixtures/lsp-lifecycle'
EXE = Path(os.environ.get('FIBRIL', ROOT / 'build/exec/fibril'))
STATES = ('Preinitialize', 'AwaitInitialized', 'Running', 'Shutdown', 'Terminated')
METHODS = ('Initialize', 'ShutdownRequest', 'OtherRequest')
NOTIFICATIONS = ('Initialized', 'Exit', 'OtherNotification')
STATE_TAG = dict(zip(STATES, (b'P', b'A', b'R', b'S', b'T')))
# Each row: initialize request, shutdown request, other request, initialized
# notification, exit notification, other notification. None means same state.
# A/N = initialize marker/null, E = error, I = ignore, X = terminate status.
TABLE = {
    'Preinitialize': (('AwaitInitialized', b'A'), (None, b'E-32002'), (None, b'E-32002'),
                      (None, b'I'), ('Terminated', b'X1'), (None, b'I')),
    'AwaitInitialized': ((None, b'E-32600'), ('Shutdown', b'N'), (None, b'E-32601'),
                         ('Running', b'I'), ('Terminated', b'X1'), (None, b'I')),
    'Running': ((None, b'E-32600'), ('Shutdown', b'N'), (None, b'E-32601'),
                (None, b'I'), ('Terminated', b'X1'), (None, b'I')),
    'Shutdown': ((None, b'E-32600'), (None, b'E-32600'), (None, b'E-32600'),
                 (None, b'I'), ('Terminated', b'X0'), (None, b'I')),
    'Terminated': ((None, b'I'), (None, b'I'), (None, b'I'),
                   (None, b'I'), (None, b'I'), (None, b'I')),
}


def checked(command, **kwargs):
    result = subprocess.run(list(map(str, command)), capture_output=True, timeout=120, **kwargs)
    if result.returncode:
        raise AssertionError((command, result.returncode, result.stdout, result.stderr))
    return result


def request(method, payload=b'1', kind='NumericId'):
    return ('Request', kind, payload, method)


def notify(method):
    return ('Notify', method)


def expected(initial, events, *, control=False):
    state, output = initial, b''
    for event in events:
        column = METHODS.index(event[3]) if event[0] == 'Request' else 3 + NOTIFICATIONS.index(event[1])
        next_state, result = TABLE[state][column]
        state = next_state or state
        response = result
        if result[:1] not in (b'I', b'X'):
            assert event[0] == 'Request'
            payload = event[2]
            assert len(payload) <= 64  # diagnostic encoding bound, not ID validation
            response = b'Q' + (b'' if control else (b'N' if event[1] == 'NumericId' else b'S') + bytes([len(payload)]) + payload) + result
        output += STATE_TAG[state] + response
    return output


def payload_source(payload):
    # Source literals, not JSON input. Source supports quote/backslash/n/r/t;
    # construct NUL using the existing octet primitive, never raw source bytes.
    parts = payload.decode('utf-8').split('\0')
    encoded = ['sourceBytes ' + json.dumps(p, ensure_ascii=False) for p in parts]
    result = encoded[-1]
    for part in reversed(encoded[:-1]):
        result = 'primBytesAppend (' + part + ') (primBytesAppend (primBytesOctetMod256 Zero) (' + result + '))'
    return result


def event_source(event):
    if event[0] == 'Notify':
        return '(Notify ' + event[1] + ')'
    assert len(event[2]) <= 64
    return '(Request (RequestDetails (' + event[1] + ' (' + payload_source(event[2]) + ')) ' + event[3] + '))'


def source_for(initial, events, *, control=False):
    # The abstract driver mentions each transition/observer once. This is a
    # fixed, finite source sequence, not an unbounded loop or transport server.
    names = ['event' + str(i) for i in range(len(events))]
    body = None
    for name in reversed(names):
        body = ('observe (next state ' + name + ') (\\(state : S) => \\(1 encoded : Bytes) => ' +
                ('primBytesAppend encoded (' + body + ')' if body else 'encoded') + ')')
    return '''module Main
import LSP
import Observation
import ControlObservation

drive : (0 S : Type) -> (0 E : Type) -> (0 O : Type) ->
  (next : (state : S) -> (event : E) -> O) ->
  (observe : (step : O) -> (consume : (state : S) -> (1 encoded : Bytes) -> Bytes) -> Bytes) ->
  (state : S) -> ''' + ''.join('(' + name + ' : E) -> ' for name in names) + '''Bytes
drive S E O next observe state ''' + ' '.join(names) + ' = ' + body + '''

main : IO Unit
main = let (sourceBytes : (text : String) -> Bytes) = \\(text : String) =>
  primUTF8Case Bytes Bytes (primUTF8Encode text) primBytesEmpty (\\(1 value : Bytes) => value) in
  primWriteBytes (drive State Event Step transition (''' + ('observeControlStep' if control else 'observeStep') + ''' Bytes) ''' + initial + ' ' + ' '.join(map(event_source, events)) + ')\n'


class LSPLifecycle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='fibril-lsp-lifecycle-')
        cls.work = Path(cls.temporary.name)
        cls.rows = []
        env = os.environ.copy()
        for key, flag in [('IDRIS2_PACKAGE_PATH', 'package-path'), ('IDRIS2_LIBS', 'libs-path'), ('IDRIS2_DATA', 'data-path')]:
            if not env.get(key):
                lines = checked(shlex.split(env.get('PACK', 'pack')) + ['--log-level=silence', flag], cwd=ROOT).stdout.decode().splitlines()
                paths = [line for line in lines if line.startswith('/')]
                if len(paths) != 1:
                    raise AssertionError(('ambiguous package paths', paths))
                env[key] = paths[0]
        env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join(p for p in env['IDRIS2_PACKAGE_PATH'].split(os.pathsep) if Path(p).parent.parent.name != 'fibril')
        stage = ROOT / 'build/test-prefix'
        assert not stage.is_symlink() and stage.resolve().is_relative_to(ROOT)
        env['IDRIS2_PREFIX'] = str(stage)
        compiler = shlex.split(env.get('IDRIS2', 'idris2'))
        installed = Path(checked(compiler + ['--dump-installdir', 'fibril.ipkg'], cwd=ROOT, env=env).stdout.decode().strip())
        assert installed.resolve().is_relative_to(stage.resolve())
        checked(compiler + ['--install', 'fibril.ipkg'], cwd=ROOT, env=env)
        env['IDRIS2_PACKAGE_PATH'] = str(installed.parent) + os.pathsep + env['IDRIS2_PACKAGE_PATH']
        shutil.copyfile(FIXTURE / 'Harness.idr', cls.work / 'Harness.idr')
        (cls.work / 'harness.ipkg').write_text('package lifecycle-harness\nsourcedir = "."\ndepends = fibril, yaml\nmain = Harness\nexecutable = harness\n')
        checked(compiler + ['--build', 'harness.ipkg'], cwd=cls.work, env=env)
        cls.hosted = cls.work / 'build/exec/harness'
        cls.cc = shlex.split(env.get('CC', 'cc'))
        cls.counter = 0

    @classmethod
    def tearDownClass(cls):
        target = os.environ.get('LSP_LIFECYCLE_EVIDENCE')
        if target:
            Path(target).write_text(json.dumps({'scope': 'validated typed events only; no parsed wire LSP', 'rows': cls.rows}, indent=2) + '\n')
        cls.temporary.cleanup()

    def source(self, source):
        type(self).counter += 1
        directory = self.work / str(self.counter)
        directory.mkdir()
        for name in ('LSP.fib', 'Observation.fib', 'ControlObservation.fib'):
            shutil.copyfile(FIXTURE / name, directory / name)
        (directory / 'Main.fib').write_text(source)
        checked([EXE, 'check', '--source-dir', directory, directory / 'Main.fib'])
        return directory

    def compile_native(self, source):
        emitted = checked([EXE, 'emit-c-binary', '--source-dir', source, source / 'Main.fib'])
        (source / 'program.c').write_bytes(emitted.stdout)
        shutil.copyfile(FIXTURE / 'SourceHarness.c', source / 'harness.c')
        checked(self.cc + ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-I', ROOT / 'runtime/native', '-I', source,
                           source / 'harness.c', '-o', source / 'native'])
        return checked([source / 'native', 'observe'])

    def both(self, label, initial, events, *, stdio=False, control=False):
        source = self.source(source_for(initial, events, control=control))
        output = expected(initial, events, control=control)
        hosted = checked([self.hosted, 'run', source, source / 'Main.fib'])
        size = re.search(rb'^SIZE (\d+) (\d+)$', hosted.stdout, re.M)
        self.assertIsNotNone(size, hosted.stdout)
        nodes, payload = map(int, size.groups())
        self.assertLessEqual(nodes, 8192)
        self.assertLessEqual(payload, 8192)
        native = self.compile_native(source)
        for backend, result in [('hosted', hosted), ('native', native)]:
            self.assertEqual(result.stderr, b'')
            self.assertIn(b'\nOK\n', result.stdout)
            actual = bytes(ast.literal_eval(re.search(rb'^OUTPUT (.*)$', result.stdout, re.M)[1].decode()))
            self.assertEqual(actual, output, (label, backend, result.stdout))
            metrics = list(map(int, re.search(rb'^METRICS ([\d ]+)$', result.stdout, re.M)[1].split()))
            self.assertEqual(metrics, [0, 1, 1] if backend == 'hosted' else [0, len(output), 1, 1, len(output)])
            cost = re.search(rb'^COST (\d+) (\d+)$', result.stdout, re.M)
            row = dict(case=label, backend=backend, initial=initial, projection='control' if control else 'full',
                       events=[list(e) if e[0] == 'Notify' else [e[0], e[1], e[2].hex(), e[3]] for e in events],
                       core_nodes=nodes, payload_estimate=payload, expected_hex=output.hex(), output_hex=actual.hex(),
                       metrics=metrics, observation=result.stdout.decode().strip())
            if cost:
                row['native_steps'], row['native_arena_payload'] = map(int, cost.groups())
            self.rows.append(row)
        if stdio:
            for command in ([EXE, 'run-binary', '--source-dir', source, source / 'Main.fib'], [source / 'native']):
                result = checked(command, input=b'')
                self.assertEqual((result.stdout, result.stderr), (output, b''))

    def test_01_complete_state_event_matrix(self):
        for state in STATES:
            for method in METHODS:
                for kind in ('NumericId', 'StringId'):
                    with self.subTest(state=state, method=method, kind=kind):
                        self.both(state + '-' + method + '-' + kind, state, [request(method, kind=kind)])
            for method in NOTIFICATIONS:
                with self.subTest(state=state, notification=method):
                    self.both(state + '-' + method, state, [notify(method)])

    def test_02_sequences(self):
        sequences = {
            'normal': [request('Initialize'), notify('Initialized'), request('ShutdownRequest', b'1', 'StringId'), notify('Exit')],
            'initialize-then-unsupported': [request('Initialize'), request('OtherRequest')],
            'shutdown-without-initialized': [request('Initialize'), request('ShutdownRequest'), notify('Initialized'), notify('Exit')],
            'duplicate-initialize-await': [request('Initialize'), request('Initialize', b'1', 'StringId')],
            'duplicate-initialize-running': [request('Initialize'), notify('Initialized'), request('Initialize')],
            'repeated-notifications': [notify('Initialized'), request('Initialize'), notify('Initialized'), notify('Initialized')],
            'preinitialize-errors': [request('OtherRequest'), request('ShutdownRequest'), notify('OtherNotification'), notify('Exit')],
            'exit-before-shutdown-await': [request('Initialize'), notify('Exit'), request('Initialize'), notify('Exit')],
            'exit-before-shutdown-running': [request('Initialize'), notify('Initialized'), notify('Exit'), request('ShutdownRequest')],
        }
        for label, events in sequences.items():
            with self.subTest(sequence=label):
                self.both(label, 'Preinitialize', events, stdio=label == 'normal', control=True)
        self.both('await-is-not-readiness-gate', 'AwaitInitialized', [request('OtherRequest'), notify('Initialized'), request('OtherRequest')], control=True)
        self.both('post-shutdown-requests', 'Shutdown', [request(m) for m in METHODS], control=True)
        self.both('terminal-absorbs', 'Terminated', [notify('Initialized'), notify('OtherNotification'), request('ShutdownRequest'), notify('Exit')], control=True)

    def test_03_opaque_id_payloads(self):
        for kind, payload in [('NumericId', b'-0'), ('NumericId', b'-2147483648'), ('NumericId', b'2147483647'),
                              ('StringId', b''), ('StringId', b'quote"\\\n\r\t'), ('StringId', b'a\0b'),
                              ('StringId', 'é😀'.encode()), ('StringId', b'x' * 64)]:
            with self.subTest(kind=kind, payload=payload):
                self.both('opaque-' + kind + '-' + payload.hex(), 'Running', [request('OtherRequest', payload, kind)])

    def test_04_pure_api_and_source_scope(self):
        result = checked([self.hosted, 'measure', FIXTURE, FIXTURE / 'Transition.fib'])
        nodes, payload = map(int, re.fullmatch(rb'SIZE (\d+) (\d+)\n', result.stdout).groups())
        self.assertLessEqual(nodes, 8192)
        self.assertLessEqual(payload, 8192)
        self.rows.append(dict(case='pure-api-admission', core_nodes=nodes, payload_estimate=payload))
        source = (FIXTURE / 'LSP.fib').read_text()
        for forbidden in ('primRead', 'primWrite', 'primFlush', 'primReject', 'primIterateBinary', 'IO '):
            self.assertNotIn(forbidden, source)
        for precondition in ('PRECONDITION (not a refinement)', 'structurally forgeable', 'No validation'):
            self.assertIn(precondition, source)

    def test_05_actual_no_output_session(self):
        source = self.source((FIXTURE / 'NoOutput.fib').read_text().replace('module NoOutput', 'module Main'))
        hosted = checked([self.hosted, 'run', source, source / 'Main.fib'])
        nodes, payload = map(int, re.search(rb'^SIZE (\d+) (\d+)$', hosted.stdout, re.M).groups())
        self.assertLessEqual(nodes, 8192)
        self.assertLessEqual(payload, 8192)
        for backend, result in [('hosted', hosted), ('native', self.compile_native(source))]:
            self.assertEqual(result.stderr, b'')
            self.assertIn(b'OUTPUT []\n', result.stdout)
            self.assertIn(b'\nOK\n', result.stdout)
            metrics = list(map(int, re.search(rb'^METRICS ([\d ]+)$', result.stdout, re.M)[1].split()))
            self.assertEqual(metrics, [0, 0, 1] if backend == 'hosted' else [0, 0, 1, 0, 0])
            self.rows.append(dict(case='actual-no-output-session', backend=backend, metrics=metrics,
                                  core_nodes=nodes, payload_estimate=payload,
                                  observation=result.stdout.decode().strip()))


if __name__ == '__main__':
    unittest.main()
