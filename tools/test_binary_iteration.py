#!/usr/bin/env python3
"""Checked source on both runners, plus separately labelled trusted C injection.

Run after a local compiler build. Installs only into build/test-prefix. Observer
copies add counters, never rewrite evaluator bodies or any admission/budget.
"""
import os
import ast
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'tools/fixtures/binary-iteration'
EXE = ROOT / 'build/exec/fibril'


def run(command, **kwargs):
    return subprocess.run(list(map(str, command)), capture_output=True, timeout=120, **kwargs)


def checked(command, **kwargs):
    result = run(command, **kwargs)
    if result.returncode:
        raise AssertionError((command, result.returncode, result.stdout, result.stderr))
    return result


def observe(work):
    for path in (ROOT / 'runtime/native').iterdir():
        if path.is_file():
            shutil.copyfile(path, work / path.name)
    path = work / 'fibril_runtime.c'
    source = path.read_text().replace('static int enter(FRuntime *r) {',
        'static size_t iteration_peak;\nstatic int enter(FRuntime *r) {')
    source = source.replace('r->steps++; r->depth++; return 1;',
        'r->steps++; r->depth++; if(r->depth>iteration_peak) iteration_peak=r->depth; return 1;')
    path.write_text(source)
    path = work / 'fibril_binary_runtime.c'
    source = path.read_text().replace('typedef struct {\n  FRuntime *runtime;',
        'static size_t iteration_callbacks, iteration_reads, iteration_writes;\ntypedef struct {\n  FRuntime *runtime;')
    source = source.replace('apply_thunk(r, step, input)', '(iteration_callbacks++, apply_thunk(r, step, input))')
    source = source.replace('FByteRead read = fibril_bytes_read(session, capacity);',
        'iteration_reads++; FByteRead read = fibril_bytes_read(session, capacity);')
    source = source.replace('FByteStatus status = fibril_bytes_write(session,',
        'iteration_writes++; FByteStatus status = fibril_bytes_write(session,')
    path.write_text(source)


class BinaryIteration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='fibril-iteration-')
        cls.work = Path(cls.temporary.name)
        env = os.environ.copy()
        pack = shlex.split(env.get('PACK', 'pack'))
        for key, command in [('IDRIS2_PACKAGE_PATH', 'package-path'), ('IDRIS2_LIBS', 'libs-path'), ('IDRIS2_DATA', 'data-path')]:
            value = env.get(key)
            if not value:
                # Pack can emit cache warnings on stdout. Never treat those as
                # paths, and never clean a shared cache to silence a warning.
                lines = checked(pack + ['--log-level=silence', command], cwd=ROOT).stdout.decode().splitlines()
                paths = [line for line in lines if line.startswith('/')]
                if len(paths) != 1:
                    raise AssertionError(('ambiguous curated paths', command, lines))
                value = paths[0]
            if key == 'IDRIS2_PACKAGE_PATH':
                value = os.pathsep.join(p for p in value.split(os.pathsep) if Path(p).parent.parent.name != 'fibril')
            env[key] = value
        stage = ROOT / 'build/test-prefix'
        if stage.is_symlink() or not stage.resolve().is_relative_to(ROOT):
            raise AssertionError('test prefix outside worktree')
        env['IDRIS2_PREFIX'] = str(stage)
        compiler = shlex.split(env.get('IDRIS2', 'idris2'))
        checked(compiler + ['--install', 'fibril.ipkg'], cwd=ROOT, env=env)
        installed = checked(compiler + ['--dump-installdir', 'fibril.ipkg'], cwd=ROOT, env=env).stdout.decode().strip()
        assert Path(installed).resolve().is_relative_to(stage.resolve())
        env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join([str(Path(installed).parent), env['IDRIS2_PACKAGE_PATH']])
        shutil.copyfile(FIXTURE / 'Hosted.idr', cls.work / 'Hosted.idr')
        (cls.work / 'hosted.ipkg').write_text('package iteration-hosted\nsourcedir = "."\ndepends = fibril, yaml\nmodules = Hosted\nmain = Hosted\nexecutable = hosted\n')
        checked(compiler + ['--build', 'hosted.ipkg'], cwd=cls.work, env=env)
        cls.compiler = compiler
        cls.environment = env
        cls.hosted = cls.work / 'build/exec/hosted'
        cls.cc = shlex.split(env.get('CC', 'cc'))
        cls.counter = 0
        cls.template = (FIXTURE / 'Main.fib').read_text()

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def source(self, source):
        type(self).counter += 1
        directory = self.work / str(self.counter)
        directory.mkdir()
        path = directory / 'Main.fib'
        path.write_text(source)
        checked([EXE, 'check', '--source-dir', directory, path])
        emitted = checked([EXE, 'emit-c-binary', '--source-dir', directory, path])
        (directory / 'program.c').write_bytes(emitted.stdout)
        observe(directory)
        shutil.copyfile(FIXTURE / 'SourceHarness.c', directory / 'harness.c')
        checked(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-I', directory,
            directory / 'harness.c', '-o', directory / 'native'])
        return directory

    def both(self, directory, mode='normal', n=1):
        results = []
        for command in ([self.hosted, directory, directory / 'Main.fib', mode, n],
                        [directory / 'native', mode, n]):
            result = checked(command)
            text = result.stdout.decode()
            metrics = tuple(map(int, re.search(r'METRICS ([\d ]+)', text)[1].split()))
            results.append((metrics, '\nOK\n' in text, text))
            print('ITERATION_ROW ' + json.dumps(dict(case=self._testMethodName, backend='hosted' if len(results) == 1 else 'native', mode=mode, input=n, observation=text.strip())), flush=True)
        return results

    def test_delimiter_1024_allowance_and_exact_overread(self):
        source = self.template.replace('"' + 'x' * 32 + '"', '"' + 'x' * 1024 + '"')
        directory = self.source(source)
        for n in (1, 31, 32, 33, 1024, 1025):
            for backend, (metrics, ok, text) in enumerate(self.both(directory, n=n)):
                self.assertEqual(ok, n <= 1024, text)
                # Hosted adapters skip empty payload writes; native observer counts descriptions.
                write_count = int(ok and (n > 1 or backend == 1))
                self.assertEqual(metrics, (min(n, 1024), write_count, int(ok), int(n > 1024), n - 1 if ok else 0), text)
            native = self.both(directory, n=n)[1][2]
            self.assertEqual(int(re.search(r'NATIVE \d+ \d+ \d+ (\d+)', native)[1]), min(n, 1024))
            budget = tuple(map(int, re.search(r'BUDGET (\d+) (\d+)', native).groups()))
            self.assertEqual(budget, (n + 1, 2 * n - 1) if n <= 1024 else (1024, 1024))
        # Real stdin is deliberately kept open: early Done must not wait for EOF.
        for command in ([EXE, 'run-binary', '--source-dir', directory, directory / 'Main.fib'], [directory / 'native']):
            for n in (1, 31, 32, 33, 1024):
                with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
                    process = subprocess.Popen(list(map(str, command)), stdin=subprocess.PIPE, stdout=out, stderr=err)
                    try:
                        process.stdin.write(b'a' * (n - 1) + b':')
                        process.stdin.flush()
                        process.wait(timeout=30)
                        out.seek(0); err.seek(0)
                        self.assertEqual((process.returncode, out.read(), err.read()), (0, b'a' * (n - 1), b''))
                    finally:
                        if process.poll() is None:
                            process.kill(); process.wait()
                        process.stdin.close()
        for mode, n, expected in [('eof', 0, (1, 0, 0, 0, 0)), ('eof', 3, (4, 0, 0, 0, 0)),
            ('read-error', 3, (2, 0, 0, 2, 0)), ('write-error', 4, (4, 1, 0, 0, 1)), ('flush-error', 4, (4, 1, 1, 0, 3))]:
            for metrics, ok, text in self.both(directory, mode, n):
                self.assertFalse(ok, text)
                self.assertEqual(metrics, expected, text)

    def test_zero_and_early_done_return_state(self):
        for count, step in [('Zero', 'primLoopContinue'), ('Succ Zero', 'primLoopDone'), ('primBytesLength (primUTF8Case Bytes Bytes (primUTF8Encode \"' + 'x' * 1024 + '\") primBytesEmpty (\\(1 b : Bytes) => b))', 'primLoopDone')]:
            source = '''module Main
main : IO Unit
main = primBind (LoopResult Bytes Bytes) Unit
  (primIterateBinary Bytes Bytes (COUNT) (\\(1 state : Bytes) => primPure (LoopStep Bytes Bytes) (STEP Bytes Bytes state)) (primBytesOctetMod256 (Succ Zero)))
  (\\(1 result : LoopResult Bytes Bytes) => primLoopResultCase Bytes Bytes (IO Unit) result (\\(1 b : Bytes) => primWriteBytes b) (\\(1 b : Bytes) => primWriteBytes b))
'''.replace('COUNT', count).replace('STEP', step)
            directory = self.source(source)
            for metrics, ok, text in self.both(directory):
                self.assertTrue(ok, text)
                self.assertEqual(metrics, (0, 1, 1, 1, 1), text)
            native = self.both(directory)[1][2]
            self.assertEqual(int(re.search(r'NATIVE \d+ \d+ \d+ (\d+)', native)[1]), int(count != 'Zero'))

    def test_count_ledger_rejects_upfront_before_callback_effects(self):
        # Compact source is checked, not a recursively rechecked unary result.
        # 3000 successors alone fit 4096; their ~6000 fold reductions do not.
        source = self.template.replace('primBytesLength (encode "' + 'x' * 32 + '")',
            '(natRec (\\(0 n : Nat) => Nat) Zero (\\(0 n : Nat) => \\(1 v : Nat) => Succ v) (primBytesLength (encode "' + 'x' * 3000 + '")))')
        directory = self.source(source)
        hosted = self.both(directory)[0]
        self.assertFalse(hosted[1], hosted[2])
        self.assertEqual(hosted[0], (0, 0, 0, 1, 0), hosted[2])
        self.assertIn('reduction budget', hosted[2])

    def test_whnf_demand_and_preserved_earlier_effects(self):
        # The expensive state has a compact, typable description; demanding its
        # WHNF fails existing fuel/depth. Marker effects must precede failure.
        expensive = 'natRec (\\(0 n : Nat) => Bytes) primBytesEmpty (\\(0 n : Nat) => \\(1 b : Bytes) => b) (primBytesLength (encode "' + 'x' * 2100 + '"))'
        prefix = self.template[:self.template.index('reject :')]
        source = prefix + r'''
step : (1 state : Bytes) -> IO (LoopStep Bytes Bytes)
step = \(1 state : Bytes) => primBind Unit (LoopStep Bytes Bytes) (primWriteBytes (encode "!"))
  (\(1 u : Unit) => case u of () => primBind Unit (LoopStep Bytes Bytes) primFlushBytes
    (\(1 v : Unit) => case v of () => primPure (LoopStep Bytes Bytes) (primLoopContinue Bytes Bytes (primBytesAppend state (EXPENSIVE)))))
main : IO Unit
main = primBind (LoopResult Bytes Bytes) Unit
  (primIterateBinary Bytes Bytes (Succ (Succ Zero)) step primBytesEmpty)
  (\(1 result : LoopResult Bytes Bytes) => primLoopResultCase Bytes Bytes (IO Unit) result (\(1 b : Bytes) => primWriteBytes b) (\(1 b : Bytes) => primWriteBytes b))
'''.replace('EXPENSIVE', expensive)
        directory = self.source(source)
        for metrics, ok, text in self.both(directory):
            self.assertFalse(ok, text)
            self.assertEqual(metrics, (0, 1, 1, 1, 1), text)
        for command in ([EXE, 'run-binary', '--source-dir', directory, directory / 'Main.fib'], [directory / 'native']):
            result = run(command, input=b'')
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'!')
            self.assertIn(b'budget', result.stderr)
        # Zero/exhausted and Done payloads are not demanded by the loop. Caller
        # consumes them syntactically behind represented rejection, no discard.
        for count, constructor in [('Zero', 'primLoopContinue'), ('Succ Zero', 'primLoopDone'), ('Succ Zero', 'primLoopContinue')]:
            source = prefix + r'''
main : IO Unit
main = primBind (LoopResult Bytes Bytes) Unit
  (primIterateBinary Bytes Bytes (COUNT) (\(1 state : Bytes) => primPure (LoopStep Bytes Bytes) (CONSTRUCTOR Bytes Bytes state)) (EXPENSIVE))
  (\(1 result : LoopResult Bytes Bytes) => primLoopResultCase Bytes Bytes (IO Unit) result
    (\(1 b : Bytes) => primBind Unit Unit (primWriteBytes (encode "!")) (\(1 u : Unit) => case u of () => primBind Unit Unit primRejectBytes (\(1 v : Unit) => case v of () => primWriteBytes b)))
    (\(1 b : Bytes) => primBind Unit Unit (primWriteBytes (encode "!")) (\(1 u : Unit) => case u of () => primBind Unit Unit primRejectBytes (\(1 v : Unit) => case v of () => primWriteBytes b))))
'''.replace('COUNT', count).replace('CONSTRUCTOR', constructor).replace('EXPENSIVE', expensive)
            directory = self.source(source)
            for metrics, ok, text in self.both(directory):
                self.assertFalse(ok, text)
                # Only zero bypasses initial WHNF. Nonzero initial is demanded.
                self.assertEqual(metrics, (0, int(count == 'Zero'), 0, 1, int(count == 'Zero')), text)
        # A normal initial followed by Done with lazy expensive R: no WHNF of R.
        source = source.replace('primLoopContinue Bytes Bytes state', 'primLoopDone Bytes Bytes (primBytesAppend state (' + expensive + '))')
        source = source.replace(')) (' + expensive + '))', ')) primBytesEmpty)')
        directory = self.source(source)
        for metrics, ok, text in self.both(directory):
            self.assertFalse(ok, text)
            self.assertEqual(metrics, (0, 1, 0, 1, 1), text)

        # Exhaustion at the final Continue does not force its returned state.
        source = source.replace('primLoopDone Bytes Bytes (primBytesAppend state (', 'primLoopContinue Bytes Bytes (primBytesAppend state (')
        directory = self.source(source)
        for metrics, ok, text in self.both(directory):
            self.assertFalse(ok, text)
            self.assertEqual(metrics, (0, 1, 0, 1, 1), text)

    def test_unused_done_branch_is_lazy_but_still_typed(self):
        expensive = 'natRec (\\(0 n : Nat) => Bytes) primBytesEmpty (\\(0 n : Nat) => \\(1 b : Bytes) => b) (primBytesLength (encode "' + 'x' * 2100 + '"))'
        source = self.template.replace('then respond (done saved)',
            'then (if True then respond (done saved) else respond (more (primBytesAppend saved (' + expensive + '))))')
        directory = self.source(source)
        for backend, (metrics, ok, text) in enumerate(self.both(directory)):
            self.assertTrue(ok, text)
            self.assertEqual(metrics, (1, backend, 1, 0, 0), text)

    def test_short_chunk_then_eof_preserves_consumed_prefix(self):
        source = self.template.replace('primReadBytes (Succ Zero)', 'primReadBytes (Succ (Succ (Succ (Succ Zero))))')
        directory = self.source(source)
        for metrics, ok, text in self.both(directory, 'eof', 3):
            self.assertFalse(ok, text)
            self.assertEqual(metrics, (2, 0, 0, 0, 0), text)

    def test_legacy_modes_reject_zero_loop_and_dormant_callback_admission(self):
        path = self.work / 'legacy.fib'
        path.write_text(r'''main : IO Unit
main = primBind (LoopResult Bytes Bytes) Unit
  (primIterateBinary Bytes Bytes Zero (\(1 s : Bytes) => primPure (LoopStep Bytes Bytes) (primLoopDone Bytes Bytes s)) primBytesEmpty)
  (\(1 r : LoopResult Bytes Bytes) => primLoopResultCase Bytes Bytes (IO Unit) r (\(1 b : Bytes) => primWriteBytes b) (\(1 b : Bytes) => primWriteBytes b))
''')
        checked([EXE, 'check', path])
        for command in ('run', 'run-interactive', 'emit-c', 'emit-c-interactive'):
            result = run([EXE, command, path])
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')
            self.assertNotIn(b'Unsupported command', result.stderr)
        # Even an unused Done branch remains subject to whole-syntax admission.
        source = self.template.replace('then respond (done saved)',
            'then (if True then respond (done saved) else primBind Unit (LoopStep Bytes Bytes) primReadLine (\\(1 u : Unit) => case u of () => respond (done saved)))')
        # Use a well-typed dormant text write, not an unrelated type error.
        source = source.replace('primReadLine', '(primWriteLine "hidden")')
        type(self).counter += 1
        directory = self.work / str(self.counter); directory.mkdir()
        path = directory / 'Main.fib'; path.write_text(source)
        checked([EXE, 'check', '--source-dir', directory, path])
        for command in ('run-binary', 'emit-c-binary'):
            result = run([EXE, command, '--source-dir', directory, path], input=b':')
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')
            self.assertIn(b'rejects', result.stderr)

    def test_linear_capture_drop_duplicate_and_mismatched_result_rejected(self):
        snippets = [
            'primIterateBinary Bytes Bytes Zero (\\(1 s : Bytes) => primPure (LoopStep Bytes Bytes) (primLoopDone Bytes Bytes (primBytesAppend s external))) primBytesEmpty',
            'primIterateBinary Bytes Bytes Zero (\\(1 s : Bytes) => primPure (LoopStep Bytes Bytes) (primLoopDone Bytes Bytes primBytesEmpty)) external',
            'primIterateBinary Bytes Bytes Zero (\\(1 s : Bytes) => primPure (LoopStep Bytes Bytes) (primLoopDone Bytes Bytes (primBytesAppend s s))) external',
            'primIterateBinary Bytes Bytes Zero (\\(1 s : Bytes) => primPure (LoopStep Bytes Unit) (primLoopContinue Bytes Unit s)) external']
        for i, expression in enumerate(snippets):
            path = self.work / f'bad{i}.fib'
            path.write_text('main : (1 external : Bytes) -> IO (LoopResult Bytes Bytes)\nmain = \\(1 external : Bytes) => ' + expression + '\n')
            result = run([EXE, 'check', path])
            self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_nested_and_two_independent_loops_share_session_work(self):
        source = r'''module Main
main : IO Unit
main = primBind (LoopResult Bytes Bytes) Unit
  (primIterateBinary Bytes Bytes (Succ (Succ (Succ Zero)))
    (\(1 state : Bytes) => primIterateBinary Bytes Bytes (Succ (Succ Zero))
      (\(1 inner : Bytes) => primPure (LoopStep Bytes Bytes) (primLoopContinue Bytes Bytes inner)) state)
    (primBytesOctetMod256 (Succ Zero)))
  (\(1 r : LoopResult Bytes Bytes) => primLoopResultCase Bytes Bytes (IO Unit) r (\(1 b : Bytes) => primWriteBytes b) (\(1 b : Bytes) => primWriteBytes b))
'''
        directory = self.source(source)
        for metrics, ok, text in self.both(directory):
            self.assertTrue(ok, text)
            self.assertEqual(metrics, (0, 1, 1, 1, 1), text)
        native = self.both(directory)[1][2]
        self.assertEqual(int(re.search(r'NATIVE \d+ \d+ \d+ (\d+)', native)[1]), 9)
        source = self.template.replace('"' + 'x' * 32 + '"', '"' + 'x' * 1024 + '"')
        final = '  bind (LoopResult Bytes Bytes) Unit\n    (primIterateBinary'
        source = source.replace(final, '  let (action : IO Unit) = bind (LoopResult Bytes Bytes) Unit\n    (primIterateBinary')
        source = source.rstrip() + ' in\n  primBind Unit Unit action (\\(1 u : Unit) => case u of () => action)\n'
        directory = self.source(source)
        hosted, native = self.both(directory, 'two', 2048)
        self.assertTrue(hosted[1], hosted[2])
        self.assertEqual(hosted[0], (2048, 2, 1, 0, 2046), hosted[2])
        self.assertFalse(native[1], native[2])
        self.assertEqual(native[0][1:3], (1, 0), native[2])
        self.assertEqual(native[0][4], 1023, native[2])
        self.assertGreater(native[0][0], 1024, native[2])
        self.assertIn('evaluation budget', native[2])
        self.assertIn('NATIVE 100000 ', native[2])

    def test_distinct_state_result_nested_variants_retain_read_slice(self):
        template = (FIXTURE / 'views/Main.fib').read_text()
        supplied = bytes([126, 0, 255, 195, 40, 128, 254, 127, 97, 98, 99])
        saved = supplied[1:6]  # NUL/FF and malformed UTF8, never decoded.
        full_limit = 'primIterateBinary Phase Reply (Succ (Succ (Succ (Succ (Succ Zero)))))'
        self.assertEqual(template.count(full_limit), 1)
        for mode, limit, prefix, callbacks in [('done', full_limit, b'D', 3),
                ('exhausted', 'primIterateBinary Phase Reply (Succ (Succ Zero))', b'E', 2)]:
            with self.subTest(transfer=mode):
                source = template.replace(full_limit, limit)
                directory = self.source(source)
                hosted, native = self.both(directory, 'views-' + mode, len(supplied))
                expected = prefix + saved
                metrics = (callbacks + 1, 1, 1, 3 - callbacks, len(expected))
                for observed, ok, text in (hosted, native):
                    self.assertTrue(ok, text)
                    self.assertEqual(observed, metrics, text)
                output = ast.literal_eval(re.search(r'OUTPUT (\[[^\n]*\])', hosted[2])[1])
                self.assertEqual(bytes(output), expected)
                self.assertLessEqual(int(re.search(r'NODES (\d+)', hosted[2])[1]), 8192)
                self.assertEqual(int(re.search(r'NATIVE \d+ \d+ \d+ (\d+)', native[2])[1]), callbacks)
                self.assertEqual(tuple(map(int, re.search(r'BUDGET (\d+) (\d+)', native[2]).groups())),
                    (callbacks + 2, 8 + callbacks + len(expected)))
                sanitized = directory / 'native-san'
                checked(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror',
                    '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-I', directory,
                    directory / 'harness.c', '-o', sanitized])
                observed = checked([sanitized, 'views-' + mode, len(supplied)])
                self.assertEqual(observed.stdout.decode(), native[2])
                self.assertEqual(observed.stderr, b'')
                # Real binary stdin/stdout on checked source, not adapter lengths.
                for command in ([EXE, 'run-binary', '--source-dir', directory, directory / 'Main.fib'],
                        [directory / 'native'], [sanitized]):
                    result = checked(command, input=supplied)
                    self.assertEqual((result.stdout, result.stderr), (expected, b''))
                # Swapping handlers is a genuine type error, unlike S=R=Bytes.
                (directory / 'Main.fib').write_text(source.replace('result finished exhausted', 'result exhausted finished'))
                wrong = run([EXE, 'check', '--source-dir', directory, directory / 'Main.fib'])
                self.assertNotEqual(wrong.returncode, 0)
                self.assertIn(b'Inferred type is not compatible', wrong.stdout + wrong.stderr)

        # Negative control: the pure length guard must demand the shared
        # slice before any callback/extra read, not just its nominal wrapper.
        slice_five = 'primBytesSlice (Succ Zero) (Succ (Succ (Succ (Succ (Succ Zero))))) chunk'
        self.assertEqual(template.count(slice_five), 1)
        directory = self.source(template.replace(slice_five,
            'primBytesSlice (Succ Zero) (Succ (Succ (Succ (Succ Zero)))) chunk'))
        guarded = self.both(directory, 'views-done', len(supplied))
        for metrics, ok, text in guarded:
            self.assertFalse(ok, text)
            self.assertEqual(metrics, (1, 0, 0, 3, 0), text)
            self.assertIn('rejected input', text)
        self.assertEqual(int(re.search(r'NATIVE \d+ \d+ \d+ (\d+)', guarded[1][2])[1]), 0)
        self.assertEqual(tuple(map(int, re.search(r'BUDGET (\d+) (\d+)', guarded[1][2]).groups())), (1, 8))

    def test_native_read_backed_view_lifetimes_and_failure_cleanup(self):
        # Last field is the bridge's latest write accepted count, including
        # successful writes; it is an error prefix specifically in mode6.
        expected = [
            (3, 4, 11, 2, 6, 2, 0, 0, 5),  # Done, explicit plus final flush
            (2, 3, 10, 2, 6, 2, 0, 0, 5),  # Exhausted, state payload consumed
            (3, 4, 11, 1, 1, 1, 0, 0, 1),  # callback rejects after marker
            (3, 4, 11, 2, 6, 1, 0, 0, 5),  # Done consumer rejects after view write
            (2, 3, 10, 2, 6, 1, 0, 0, 5),  # Exhausted consumer rejects
            (3, 4, 11, 1, 1, 1, 0, 1, 1),  # physical read error with prefix1
            (3, 4, 11, 2, 3, 1, 0, 0, 2),  # physical write error accepted prefix2
            (3, 4, 11, 2, 6, 2, 0, 0, 5),  # final flush failure
            (1, 1, 8, 1, 1, 1, 0, 0, 1),   # first explicit flush failure
        ]
        for sanitize in (False, True):
            target = self.work / ('view-lifetime-san' if sanitize else 'view-lifetime')
            flags = ['-fsanitize=address,undefined', '-fno-omit-frame-pointer'] if sanitize else []
            checked(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-I', ROOT / 'runtime/native',
                *flags, FIXTURE / 'ViewLifetime.c', '-o', target])
            for mode, counts in enumerate(expected):
                with self.subTest(sanitize=sanitize, mode=mode):
                    result = checked([target, mode])
                    self.assertEqual(result.stderr, b'')
                    fields = result.stdout.decode().split()
                    self.assertEqual(fields[:2], ['VIEW_LIFETIME', str(mode)])
                    self.assertEqual(tuple(map(int, fields[2:])), counts)
                    print(('SAN ' if sanitize else 'RAW ') + result.stdout.decode(), end='', flush=True)

    def test_source_count_parameter_is_unrestricted(self):
        path = self.work / 'linear-count.fib'
        path.write_text(r'''main : (1 count : Nat) -> IO (LoopResult Bytes Bytes)
main = \(1 count : Nat) => primIterateBinary Bytes Bytes count (\(1 s : Bytes) => primPure (LoopStep Bytes Bytes) (primLoopDone Bytes Bytes s)) primBytesEmpty
''')
        result = run([EXE, 'check', path])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'usage', (result.stdout + result.stderr).lower())

    def test_raw_trusted_fixtures_sanitized(self):
        for sanitize in (False, True):
            target = self.work / ('raw-san' if sanitize else 'raw')
            flags = ['-fsanitize=address,undefined', '-fno-omit-frame-pointer'] if sanitize else []
            checked(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-I', ROOT / 'runtime/native', *flags, FIXTURE / 'Raw.c', '-o', target])
            for mode in range(15):
                with self.subTest(sanitize=sanitize, mode=mode):
                    result = checked([target, mode])
                    self.assertEqual((result.stdout, result.stderr), (b'', b''))


if __name__ == '__main__':
    unittest.main()
