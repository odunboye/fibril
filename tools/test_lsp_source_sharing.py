#!/usr/bin/env python3
"""Offline regressions for the two-alias candidate, not a grammar formal proof."""
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import probe_lsp_source_sharing as probe

from lsp_source_sharing import (ROOT, CANDIDATE, BASELINES, source_preservation,
    bare, closed, expand_closed, expand_introduced, instrument_module_check)

EVIDENCE = ROOT / 'docs/assets/evidence/lsp-source-sharing.json'
PRE_ROUTING_FIX_COMMIT = '840ba8f'
HISTORICAL_HARNESS_PATHS = {'tools/probe_lsp_source_sharing.py', 'tools/test_lsp_source_sharing.py'}


def historical_bytes(path):
    result = probe.run_process(['git', '-C', str(ROOT), 'show', f'{PRE_ROUTING_FIX_COMMIT}:{path}'], timeout=10)
    if result.returncode:
        raise AssertionError(result.stderr)
    return result.stdout


def node(tag, detail=None, children=None):
    return dict(tag=tag, detail=detail or [], children=children or [])


def variable(index):
    return node('Variable', [index])


class LSPSourceSharing(unittest.TestCase):
    def test_source_inverse_is_exact_and_token_safe(self):
        for name in BASELINES:
            self.assertTrue(source_preservation(name))
            text = (CANDIDATE / f'Protocol/{name}.fib').read_text()
            for changed in (text.replace('then', 'else', 1), text + '\n',
                            text.replace('let (shared', 'let (1 shared', 1)):
                with self.assertRaises(AssertionError):
                    source_preservation(name, changed)
        # Not regex counts: literals/comments/other names are not reference rewrites.
        text = (CANDIDATE / 'Protocol/JSON.fib').read_text()
        for changed in (text.replace('"!"', '"sharedOrBool"', 1), text + '-- sharedOrBool\n'):
            with self.assertRaises(AssertionError):
                source_preservation('JSON', changed)
        original = BASELINES['JSON'].read_text()
        self.assertIn('let (sameText : (1 left : String) -> (1 right : String) -> Bool) = equalString in', original)

    def test_all_other_candidate_files_are_byte_copies(self):
        origins = {
            'examples/modules/binary-frame': ('Main.fib', 'Two.fib'),
            'tools/fixtures/json-iteration': ('Parse.fib', 'ParseBinary.fib', 'Read65.fib', 'PureRead65.fib', 'Hosted.idr', 'SourceHarness.c'),
            'tools/fixtures/lsp-lifecycle': ('LSP.fib', 'Observation.fib', 'ControlObservation.fib'),
            'tools/fixtures/lsp-cost-audit': ('EchoThenTyped.fib', 'JSONThenTyped.fib')}
        for origin, files in origins.items():
            for file in files:
                self.assertEqual((CANDIDATE / file).read_bytes(), (ROOT / origin / file).read_bytes(), file)

    def test_capture_safe_binder_removal_and_outer_index_shifts(self):
        rhs = node('Lambda', [1], [node('BoolType'), variable(0)])
        self.assertTrue(closed(rhs))
        self.assertFalse(closed(variable(0)))
        # Under each intrinsic binder, local 0 stays 0, alias 1 gets the closed
        # function, outer 2 becomes 1. Annotation remains outside that binder.
        for tag in ('Lambda', 'Pi', 'Sigma'):
            body = node(tag, [2], [variable(0), node('Apply', children=[
                variable(0), node('Apply', children=[variable(1), variable(2)])])])
            expanded = expand_closed(body, rhs)
            self.assertEqual(bare(expanded['children'][0]), bare(rhs))
            local, application = expanded['children'][1]['children']
            self.assertEqual(local, variable(0))
            self.assertEqual(bare(application['children'][0]), bare(rhs))
            self.assertEqual(application['children'][1], variable(1))
        self.assertEqual(expand_closed(variable(1), rhs), variable(0))

    def test_only_verified_closed_unrestricted_alias_is_expanded(self):
        boolean = node('BoolType')
        ty = node('Pi', [1], [boolean, node('Pi', [1], [boolean, boolean])])
        rhs = node('Apply', children=[node('Lambda', [1], [ty, variable(0)]),
            node('Lambda', [1], [boolean, node('Lambda', [1], [boolean, variable(0)])])])
        alias = node('Apply', children=[node('Lambda', [2], [ty, variable(0)]), rhs])
        expanded, count = expand_introduced(alias, rhs)
        self.assertEqual(count, 1)
        self.assertEqual(bare(expanded), bare(rhs))
        with self.assertRaises(AssertionError):
            expand_introduced(node('Apply', children=[node('Lambda', [2], [ty, variable(0)]), variable(0)]), variable(0))
        linear = copy.deepcopy(alias); linear['children'][0]['detail'] = [1]
        with self.assertRaises(AssertionError):
            expand_introduced(linear, rhs)
        # Arbitrary beta-redexes cannot serve as a grammar equivalence oracle.
        with self.assertRaises(AssertionError):
            expand_introduced(node('Apply', children=[node('Lambda', [2], [boolean, variable(0)]), boolean]), rhs)

    def test_counter_clone_seams_fail_closed_and_decisions_unchanged(self):
        source = (ROOT / 'src/Fibril/Driver/ModuleCheck.idr').read_text()
        clone = instrument_module_check(source)
        self.assertEqual(re.findall(r'^\s*if .+ then', source, re.M), re.findall(r'^\s*if .+ then', clone, re.M))
        for seam in ('compileDeclarations snapshot name (local :: qualified :: globals) rest (minus remaining estimate)',
                     'if main.size > compiled.remaining', 'compileGraph True graph prelude [] 200000 [] graph.modules',
                     'checkRuntime checkingDepth typeReductionFuel Empty value ty'):
            self.assertEqual(source.count(seam), 1)
            self.assertEqual(clone.count(seam), 1)
        with self.assertRaises(AssertionError):
            instrument_module_check(source.replace('module Fibril.Driver.ModuleCheck', 'module Changed'))

    def test_evidence_exact_sizes_construction_and_blockers(self):
        data = json.loads(EVIDENCE.read_text())
        sanitized = json.loads(EVIDENCE.with_name('lsp-source-sharing-sanitized.json').read_text())
        for key in ('syntax', 'helpers', 'native', 'json_rows', 'json_matrix_totals', 'framing',
                    'inputs_sha256', 'private_checker_sha256', 'source_controls'):
            self.assertEqual(data[key], sanitized[key], key)
        # Runtime observations predate the harness-only routing fix. Preserve
        # their hashes and verify those two historical blobs, not rewritten hashes.
        for path in (EVIDENCE, EVIDENCE.with_name('lsp-source-sharing-sanitized.json')):
            self.assertEqual(path.read_bytes(), historical_bytes(path.relative_to(ROOT)))
        for path, sha in data['inputs_sha256'].items():
            content = historical_bytes(path) if path in HISTORICAL_HARNESS_PATHS else (ROOT/path).read_bytes()
            self.assertEqual(hashlib.sha256(content).hexdigest(), sha, path)
        rows = {r['entry']: r for r in data['syntax']}
        expected = {'Main.fib': (4341, 3719, 52863, 51509), 'Two.fib': (4364, 3742, 52909, 51555),
            'Parse.fib': (6205, 4935, 145990, 136828), 'ParseBinary.fib': (7467, 6197, 148514, 139352),
            'PureRead65.fib': (6674, 5404, 164522, 155360), 'Read65.fib': (8002, 6732, 167178, 158016),
            'EchoThenTyped.fib': (11403, 10781, 186813, 185459)}
        for name, (old, new, debit_old, debit_new) in expected.items():
            row = rows[name]
            self.assertEqual((row['baseline']['core_nodes'], row['candidate']['core_nodes']), (old,new))
            self.assertEqual((row['baseline']['construction_debit'], row['candidate']['construction_debit']), (debit_old,debit_new))
            self.assertEqual(row['baseline']['payload'], row['candidate']['payload'])
            self.assertTrue(row['checked_alias_expansion_exact'])
            self.assertEqual(row['introduced_binders'], 1)
            for label in ('baseline', 'candidate'):
                entry = row[label]
                self.assertEqual(entry['construction_debit'], entry['declaration_debit'] + entry['main_reservation'])
                self.assertEqual(entry['main_reservation'], entry['core_nodes'])
        self.assertIn('node-admission-blocker', rows['EchoThenTyped.fib']['candidate']['native_admission'])
        for label, remaining in [('baseline', 7778), ('candidate',14400)]:
            entry = rows['JSONThenTyped.fib'][label]
            self.assertIsNone(entry['core_nodes'])
            self.assertIn('remaining=' + str(remaining), entry['diagnostic'])
            self.assertIn('declaration_estimate=' + str(remaining+13), entry['diagnostic'])
            self.assertIn('construction-blocker', entry['native_admission'])

    def test_executed_matrix_gates_and_full_framing_are_evidence(self):
        data = json.loads(EVIDENCE.read_text())
        self.assertEqual(data['json_matrix_totals'], {b:{'valid_transfer':76,'invalid_json':43,'reader_eof':1} for b in ('hosted','native')})
        self.assertEqual(data['framing']['regressions'], 14)
        self.assertEqual(data['framing']['failures'], 0)
        self.assertEqual({r['case'] for r in data['source_controls']}, {'malformed','missing-helper','non-alias-body-change'})
        matrix = [r for r in data['json_rows'] if 'category' in r]
        self.assertEqual(len(matrix), 240)
        for row in matrix:
            self.assertNotEqual(row['category'], 'budget_rejection')
            if row['backend'] == 'hosted':
                self.assertIn('INTERACTIVE_GATE rejected', row['observation'])
                self.assertIn('RESOURCE_GATE rejected', row['observation'])
            if row['category'] != 'reader_eof':
                self.assertEqual(row['stdout_hex'], row['expected_hex'])
        controls = [r for r in data['json_rows'] if r['case'] == 'no-parser-transport']
        self.assertEqual(len(controls), 2)
        for row in controls:
            self.assertIn('METRICS 0 0 1 0 0', row['observation'])

    def test_native_profiles_balance_and_unchanged_effect_ledgers(self):
        data = json.loads(EVIDENCE.read_text())
        self.assertEqual(len(data['native']), 10)
        for row in data['native']:
            metrics, attr = row['metrics'], row['attribution']
            self.assertEqual(sum(attr['steps'].values()), metrics['steps'])
            self.assertEqual(sum(a[1] for a in attr['allocations'].values()), metrics['arena_payload'])
            self.assertEqual(sum(attr['values'].values()), attr['allocations']['new_value'][0])
            self.assertTrue(row['observer_equal'])
            if row['entry'].endswith('candidate'):
                old = next(r for r in data['native'] if r['entry'] == row['entry'].replace('candidate','baseline') and r['case'] == row['case'])
                for key in ('callbacks','reads','writes','consumed_bytes','accepted_bytes','flushes','requests','reserved_capacity','peak_pure_depth'):
                    self.assertEqual(metrics[key], old['metrics'][key])
                self.assertEqual(row['output_sha256'], old['output_sha256'])
        dense = next(r for r in data['native'] if r['entry']=='JSON-candidate' and r['case']=='64-token-array')
        self.assertEqual((dense['metrics']['steps'], dense['metrics']['arena_payload']), (95602,2894705))


def routing_attributes(j, f):
    return [(module, name, getattr(module, name)) for module, names in
            ((j, ('FIXTURE', 'checked', 'subprocess')),
             (f, ('SOURCE', 'ENTRY', 'run', 'subprocess'))) for name in names]


class LSPSourceSharingRouting(unittest.TestCase):
    def test_existing_cli_gate_and_three_framing_compilers_delegate(self):
        import test_json_iteration as j
        import test_framing as f
        saved = routing_attributes(j, f)
        original_run, original_popen = subprocess.run, subprocess.Popen
        calls = []

        def owned(command, *, input=None, timeout=120):
            calls.append((command, input, timeout))
            if 'emit-c-binary' in command:
                output = b' '.join((b'f_read_bytes(', b'f_write_bytes(', b'f_reject_bytes(',
                                    b'f_nominal_case(', b'f_bytes_length_is('))
            elif '-std=c11' in command:
                output = b''  # All three actual setup call sites, no compiler executed.
            elif 'run' in command or 'emit-c' in command:
                return subprocess.CompletedProcess(command, 1, b'', b'Gate rejected input')
            else:
                output = b'METRICS 0 0 1 0 0\nOUTPUT []\nOK\n'
                output += b'CALLBACK\n' * 4 if command[0] == '/routing-hosted' else b'NATIVE 0 0 0 4\n'
            return subprocess.CompletedProcess(command, 0, output, b'')

        class OfflineJSON(j.JSONIteration):
            hosted = Path('/routing-hosted')
            rows = []

            @classmethod
            def source(cls, entry, module=None):
                return CANDIDATE  # Routing test only: no source or compiler execution.

        class OfflineFraming(f.Framing):
            pass

        with mock.patch.object(probe, 'run_process', side_effect=owned):
            with probe.candidate_suite_routing({}):
                self.assertIs(j.FIXTURE, CANDIDATE)
                self.assertIs(f.SOURCE, CANDIDATE)
                self.assertEqual(f.ENTRY, CANDIDATE / 'Main.fib')
                self.assertIs(j.subprocess.Popen, original_popen)
                self.assertIs(f.subprocess.Popen, original_popen)
                self.assertIs(f.subprocess.PIPE, subprocess.PIPE)
                self.assertIs(subprocess.run, original_run)
                self.assertIs(subprocess.Popen, original_popen)
                OfflineJSON('test_no_parser_transport_and_existing_mode_gates').test_no_parser_transport_and_existing_mode_gates()
                try:
                    OfflineFraming.setUpClass()
                finally:
                    OfflineFraming.doClassCleanups()
        self.assertEqual(len(calls), 9)
        self.assertEqual([timeout for command, _, timeout in calls if 'run' in command or 'emit-c' in command], [30, 30])
        self.assertEqual([timeout for command, _, timeout in calls if '-std=c11' in command], [90, 90, 90])
        self.assertEqual([timeout for command, _, timeout in calls if 'emit-c-binary' in command], [90, 90])
        self.assertEqual([timeout for command, _, timeout in calls if command[0] == '/routing-hosted' or command[0] == str(CANDIDATE / 'native')], [120, 120])
        for module, name, original in saved:
            self.assertIs(getattr(module, name), original)
        self.assertIs(subprocess.run, original_run)
        self.assertIs(subprocess.Popen, original_popen)

    def test_proxy_preserves_results_and_rejects_unsupported_options(self):
        result = subprocess.CompletedProcess([], 7, b'output\0', b'error\0')
        command = ['/candidate-command']
        with mock.patch.object(probe, 'run_process', return_value=result) as owned:
            proxy = probe.CapturedSubprocessProxy(subprocess)
            actual = proxy.run(command, capture_output=True, timeout=30, input=b'input\0',
                               cwd=ROOT, env={'ROUTING_TEST': 'value'})
            self.assertIs(actual.args, command)
            self.assertEqual((actual.returncode, actual.stdout, actual.stderr), (7, b'output\0', b'error\0'))
            args, kwargs = owned.call_args
            self.assertEqual(kwargs, {'input': b'input\0', 'timeout': 30})
            self.assertEqual(args[0][-4:], ['env', '-i', 'ROUTING_TEST=value', '/candidate-command'])
            self.assertIn(str(ROOT), args[0])
            with self.assertRaises(AssertionError):
                probe.process(command)
            before = owned.call_count
            for option in ('check', 'shell', 'text', 'stdout', 'stderr', 'stdin'):
                with self.assertRaises(TypeError):
                    proxy.run(command, capture_output=True, timeout=30, **{option: True})
            with self.assertRaises(ValueError):
                proxy.run(command, capture_output=False, timeout=30)
            for timeout in (None, 0, float('inf')):
                with self.assertRaises(ValueError):
                    proxy.run(command, capture_output=True, timeout=timeout)
            with self.assertRaises(TypeError):
                proxy.run(command, capture_output=True, timeout=30, input='not bytes')
            self.assertEqual(owned.call_count, before)
        failure = subprocess.TimeoutExpired(command, 30, output=b'partial', stderr=b'diagnostic')
        with mock.patch.object(probe, 'run_process', side_effect=failure):
            with self.assertRaises(subprocess.TimeoutExpired) as raised:
                proxy.run(command, capture_output=True, timeout=30)
        self.assertIs(raised.exception, failure)

    def test_suite_attributes_restore_on_assertion_and_timeout(self):
        import test_json_iteration as j
        import test_framing as f
        saved = routing_attributes(j, f)
        original_run, original_popen = subprocess.run, subprocess.Popen
        for failure in (AssertionError('suite failed'), subprocess.TimeoutExpired(['owned-child'], 30)):
            with mock.patch.object(probe, 'run_candidate_suites', side_effect=failure):
                with self.assertRaises(type(failure)):
                    probe.suites({})
            for module, name, original in saved:
                self.assertIs(getattr(module, name), original)
            self.assertIs(subprocess.run, original_run)
            self.assertIs(subprocess.Popen, original_popen)

    def test_proxy_tiny_owned_child_captures_bytes_environment_and_cwd(self):
        proxy = probe.CapturedSubprocessProxy(subprocess)
        with tempfile.TemporaryDirectory(prefix='fibril-routing-test-') as work:
            code = ('import os,sys; data=sys.stdin.buffer.read(); '
                    'os.write(1, data + os.environ["ROUTING_TEST"].encode() + os.getcwd().encode()); '
                    'os.write(2, b"error\\0"); sys.exit(7)')
            result = proxy.run([sys.executable, '-c', code], capture_output=True, timeout=5,
                               input=b'input\0', cwd=work, env={'ROUTING_TEST': 'value'})
            self.assertEqual(result.returncode, 7)
            self.assertEqual(result.stdout, b'input\0value' + str(Path(work).resolve()).encode())
            self.assertEqual(result.stderr, b'error\0')


if __name__ == '__main__':
    unittest.main()
