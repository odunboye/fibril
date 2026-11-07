#!/usr/bin/env python3
"""Source/observer tests, not acceptance of generalized production framing.

Long native observations may be budget blocked. Such rows are reported, never
asserted as permanent failures or counted as successful parser executions.
"""
import json
import os
from pathlib import Path
import shlex
import tempfile
import unittest

from probe_header_iteration import (FIXTURE, METRICS, ROOT, VARIANTS, instrument,
                                    native_metrics, replace_exact, source_variant)
from probe_header_loops import invoke


class HeaderIterationProbeTests(unittest.TestCase):
    def test_preserved_hot_source_is_only_alias_and_dispatch_specialization(self):
        source = (FIXTURE / 'Main.fib').read_text()
        hot = source_variant(source, 'value-first')
        self.assertEqual(hot, (FIXTURE.parent / 'value-first/Main.fib').read_text())
        self.assertEqual(source_variant(source, 'baseline'), source)
        for variant in ('aliases', 'value-first'):
            specialized = source_variant(source, variant)
            start, end = source.index('  let (table : '), source.index('  let (respond : ')
            self.assertIn(source[start:end], specialized)
            self.assertIn('if same lines "xxxxxxxxxxxxxxxx" then reject', specialized)
            self.assertIn('primIterateBinary S Bytes', specialized)
        self.assertIn(r'if same c "\r" then more "lf"', hot)
        self.assertNotIn(r'if same c "\\r"', hot)

    def test_weakened_controls_are_explicit_and_never_production_sources(self):
        source = (FIXTURE / 'Main.fib').read_text()
        for variant in VARIANTS:
            transformed = source_variant(source, variant)
            if 'classification-control' in variant:
                self.assertIn('=> ascii bytes in', transformed)
                self.assertNotIn('=> primBytesIndexCase String', transformed)
            else:
                self.assertIn('=> primBytesIndexCase String', transformed)
        with self.assertRaises(ValueError):
            source_variant(source, 'unknown')

    def test_observer_only_changes_private_copies_and_keeps_limits(self):
        originals = {p.name: p.read_bytes() for p in (ROOT / 'runtime/native').iterdir() if p.is_file()}
        with tempfile.TemporaryDirectory() as temporary:
            work = Path(temporary)
            instrument(work)
            for name in ('fibril_runtime.c', 'fibril_binary_runtime.c'):
                before = originals[name].decode()
                after = (work / name).read_text()
                self.assertEqual([s for s in before.splitlines() if s.startswith('#define F_MAX_')],
                                 [s for s in after.splitlines() if s.startswith('#define F_MAX_')])
            self.assertEqual((work / 'fibril_binary_runtime.c').read_text().count('probe_callbacks++'), 2)
        for name, original in originals.items():
            self.assertEqual((ROOT / 'runtime/native' / name).read_bytes(), original)

    def test_observer_seams_and_metrics_fail_closed(self):
        for source in ('absent', 'seam seam'):
            with self.assertRaises(ValueError):
                replace_exact(source, 'seam', 'new')
        self.assertEqual(replace_exact('aa', 'a', 'b', count=2), 'bb')
        row = b'HEADER_ITERATION_METRICS 1 2 3 4 5 6 7 8 9 10\n'
        self.assertEqual(native_metrics(row)['flushes'], 10)
        for data in (b'', row + row, b'HEADER_ITERATION_METRICS 1\n'):
            with self.assertRaises(ValueError):
                native_metrics(data)


class HeaderIterationSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='fibril-header-source-')
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.commands = []
        compiler = ROOT / 'build/exec/fibril'
        for variant in ('baseline', 'value-first'):
            root = FIXTURE if variant == 'baseline' else FIXTURE.parent / 'value-first'
            project = ['--source-dir', str(root), str(root / 'Main.fib')]
            checked = invoke([str(compiler), 'check', *project], timeout=30)
            if checked[0] or checked[3]:
                raise AssertionError(checked)
            emitted = invoke([str(compiler), 'emit-c-binary', *project], timeout=30)
            if emitted[0] or emitted[3]:
                raise AssertionError(emitted)
            work = Path(cls.temporary.name) / variant
            work.mkdir()
            (work / 'main.c').write_bytes(emitted[1])
            instrument(work)
            (work / 'metrics.c').write_text(METRICS)
            built = invoke(shlex.split(os.environ.get('CC', 'cc')) + [
                '-std=c11', '-Wall', '-Wextra', '-Werror', '-I', str(work),
                str(work / 'main.c'), str(work / 'metrics.c'), '-o', str(work / 'native')], timeout=90)
            if built[0] or built[3]:
                raise AssertionError(built)
            cls.commands.extend([(variant, 'hosted', [str(compiler), 'run-binary', *project]),
                                 (variant, 'native', [str(work / 'native')])])

    def observe(self, variant, backend, command, data):
        result = invoke(command, data, timeout=30, open_stdin=True)
        self.assertFalse(result[3], (variant, backend, 'TIMEOUT', result))
        self.assertNotIn(b'Sanitizer', result[2])
        self.assertNotIn(b'runtime error:', result[2])
        metrics = native_metrics(result[2]) if backend == 'native' else None
        return result, metrics

    def accept(self, data):
        for variant, backend, command in self.commands:
            result, metrics = self.observe(variant, backend, command, data)
            self.assertEqual(result[:2], (0, data), (variant, backend, result))
            if metrics:
                self.assertEqual((metrics['callbacks'], metrics['reads'], metrics['writes'],
                                  metrics['requests'], metrics['reserved_capacity'],
                                  metrics['consumed_bytes'], metrics['accepted_bytes'], metrics['flushes']),
                                 (len(data), len(data), 1, len(data) + 1, 2 * len(data), len(data), len(data), 1))
            else:
                self.assertEqual(result[2], b'')

    def reject(self, data):
        for variant, backend, command in self.commands:
            result, metrics = self.observe(variant, backend, command, data)
            self.assertNotEqual(result[0], 0, (variant, backend, result))
            self.assertEqual(result[1], b'')
            self.assertIn(b'Binary program rejected input', result[2])
            if metrics:
                self.assertEqual((metrics['writes'], metrics['accepted_bytes'], metrics['flushes']), (0, 0, 0))

    def test_short_ascii_names_values_and_strict_crlf(self):
        for data in (b'\r\n', b'Content-Length: 0\r\n\r\n',
                     b'cOnTeNt-LeNgTh: 1\r\nX-Unknown: Mixed CASE []={}\r\n\r\n'):
            self.accept(data)
        tokens = b"!#$%&'*+-.^_`|~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
        for start in range(0, len(tokens), 8):
            self.accept(tokens[start:start + 8] + b':\r\n\r\n')
        # This is a lexer diagnostic: missing/duplicate CL are NOT validated.
        self.accept(b'X: value\r\n\r\n')
        self.accept(b'Content-Length: 1\r\ncontent-length: 2\r\n\r\n')

    def test_long_name_budget_observation_is_not_a_golden_failure(self):
        data = b"!#$%&'*+-.^_`|~0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz:\r\n\r\n"
        for variant, backend, command in self.commands:
            result, metrics = self.observe(variant, backend, command, data)
            blocked = b'budget exhausted' in result[2]
            print('HEADER_OBSERVATION ' + json.dumps(dict(case='long-name-' + str(len(data)),
                variant=variant, backend=backend, outcome='budget-blocked-NOT-parser-success' if blocked else 'accepted',
                diagnostic=result[2].decode(), metrics=metrics)), flush=True)
            if blocked:
                self.assertNotEqual(result[0], 0)
                self.assertEqual(result[1], b'')
                if metrics:
                    self.assertEqual(metrics['flushes'], 0)
            else:
                self.assertEqual(result[:2], (0, data))

    def test_invalid_ascii_tokens_controls_and_crlf_reject_with_stdin_open(self):
        for data in (b':', b'X ', b'X@', b'X\t', b'X\x7f', b'X\xff', b'X\x00',
                     b'X:\x00', b'X:\t', b'X:\x7f', b'X:\xff', b'X:\xc3',
                     b'X:\n', b'X:\rX', b'X\r', b'\n', b'\rX'):
            self.reject(data)

    def test_truncated_headers_reject_without_output(self):
        data = b'X: a\r\n\r\n'
        for length in range(len(data)):
            # Close stdin for truncation; unlike live invalid-prefix rejection.
            for variant, backend, command in self.commands:
                result = invoke(command, data[:length], timeout=30)
                self.assertFalse(result[3], (variant, backend, result))
                self.assertNotEqual(result[0], 0)
                self.assertEqual(result[1], b'')
                self.assertIn(b'Binary program rejected input', result[2])

    def test_nonempty_header_line_allowance_15_16_17(self):
        for count in (15, 16):
            self.accept(b'X:\r\n' * count + b'\r\n')
        self.reject(b'X:\r\n' * 17 + b'\r\n')

    def test_total_header_allowance_observations_are_not_golden_budget_failures(self):
        cases = [('one-line-' + str(n), b'X:' + b'a' * (n - 6) + b'\r\n\r\n')
                 for n in (1023, 1024, 1025)]
        cases += [('two-lines-1024', b'X:' + b'a' * 496 + b'\r\nY:' + b'b' * 518 + b'\r\n\r\n'),
                  ('two-lines-1025', b'X:' + b'a' * 496 + b'\r\nY:' + b'b' * 519 + b'\r\n\r\n')]
        for name, data in cases:
            for variant, backend, command in self.commands:
                result, metrics = self.observe(variant, backend, command, data)
                blocked = b'native evaluation budget exhausted' in result[2]
                print('HEADER_OBSERVATION ' + json.dumps(dict(case=name, variant=variant, backend=backend,
                    outcome='budget-blocked-NOT-parser-success' if blocked else 'accepted' if result[0] == 0 else 'input-rejected',
                    metrics=metrics)), flush=True)
                if blocked:
                    self.assertEqual(backend, 'native')
                    self.assertNotEqual(result[0], 0)
                    self.assertEqual(result[1], b'')
                    self.assertLessEqual(metrics['consumed_bytes'], 1024)
                    self.assertEqual((metrics['writes'], metrics['accepted_bytes'], metrics['flushes']), (0, 0, 0))
                elif len(data) <= 1024:
                    self.assertEqual(result[:2], (0, data))
                    if metrics:
                        self.assertEqual(metrics['consumed_bytes'], len(data))
                else:
                    self.assertNotEqual(result[0], 0)
                    self.assertEqual(result[1], b'')
                    self.assertIn(b'Binary program rejected input', result[2])
                    if metrics:
                        self.assertEqual((metrics['reads'], metrics['consumed_bytes'], metrics['flushes']), (1024, 1024, 0))


if __name__ == '__main__':
    unittest.main()
