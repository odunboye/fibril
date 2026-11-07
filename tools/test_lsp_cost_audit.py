#!/usr/bin/env python3
"""Offline audit regression tests, not a protocol integration acceptance suite."""
from pathlib import Path
import re
import tempfile
import unittest

from probe_lsp_cost_audit import ROOT, FIXTURE, summarize, prepare_root
from lsp_cost_instrument import instrument, replace_once
from test_lsp_lifecycle import source_for, request, notify
from test_binary_iteration import observe
from lsp_evidence_history import verify_evidence

EVIDENCE = ROOT / 'docs/assets/evidence/lsp-cost-audit.json'


class LSPCostAudit(unittest.TestCase):
    def test_inventory_coverage_and_existing_quantity_rules(self):
        source = (FIXTURE / 'Audit.idr').read_text()
        patterns = re.findall(r'^  dump context role (.+?) =', source, re.M)
        size = (ROOT / 'src/Fibril/Core/Size.idr').read_text().split('  variantArmNodes :')[0]
        expected = re.findall(r'^  coreNodes (.+?) =', size, re.M)
        tag = lambda pattern: pattern.lstrip('(').split()[0].rstrip(')')
        self.assertEqual([tag(p) for p in patterns], [tag(p) for p in expected])
        self.assertIn('inferErased 512 128 context fun', source)
        self.assertIn('HeadForm (Pi Erased _ _)', source)
        self.assertIn('dump (Extend context q a) "computational" b', source)
        self.assertIn('(applicationRole context a) b', source)
        self.assertIn('fieldRole ty index', source)
        self.assertNotIn('Fibril.Driver.Native.Emit', source)

    def test_compatibility_tree_cannot_be_reported_as_shared_admission(self):
        with self.assertRaisesRegex(ValueError, 'shared-graph admission'):
            summarize({'representation': 'bounded-global-expansion'})

    def test_disjoint_roles_and_list_cell_accounting(self):
        def node(tag, role='computational', children=None, literal=0, nominal=0):
            return dict(tag=tag, role=role, children=children or [], literal=literal, nominal=nominal)
        tree = node('Apply', children=[node('Lambda', children=[node('NatType', 'metadata'), node('Variable')]),
            node('ListCell', 'erased_argument', [node('StringValue', literal=3)])])
        row = summarize(dict(tree=tree, core_nodes=6, payload_estimate=3))
        self.assertEqual(row['roles'], {'computational': 3, 'metadata': 1, 'erased_argument': 2})
        self.assertEqual(sum(row['categories'].values()), 6)
        with self.assertRaises(AssertionError):
            summarize(dict(tree=tree, core_nodes=5, payload_estimate=3))
        left, right = node('Variable'), node('Variable')
        left['detail'], right['detail'] = [0], [1]
        for _ in range(20):
            left, right = node('NatSucc', children=[left]), node('NatSucc', children=[right])
        row = summarize(dict(tree=node('Apply', children=[left, right]), core_nodes=43, payload_estimate=0))
        self.assertTrue(row['repeated_shapes_not_dedup_savings'])
        self.assertEqual(row['repeated_syntax_not_dedup_savings'], [])

    def test_fixtures_are_honest_and_full_ids_not_control_projection(self):
        expected = source_for('Preinitialize', [request('Initialize'), notify('Initialized'),
                              request('ShutdownRequest', b'1', 'StringId'), notify('Exit')])
        self.assertEqual((FIXTURE / 'FullIdFour.fib').read_text(), expected.replace('module Main', 'module FullIdFour', 1))
        self.assertIn('(observeStep Bytes)', expected)
        with tempfile.TemporaryDirectory() as temporary:
            root = prepare_root(Path(temporary))
            self.assertEqual((root / 'Protocol/Frame.fib').read_bytes(),
                             (ROOT / 'examples/modules/binary-frame/Protocol/Frame.fib').read_bytes())
            self.assertEqual((root / 'Protocol/JSON.fib').read_bytes(),
                             (ROOT / 'tools/fixtures/json-iteration/Protocol/JSON.fib').read_bytes())
        for filename in ('EchoThenTyped.fib', 'JSONThenTyped.fib', 'EchoJSONThenTyped.fib'):
            self.assertIn('ADMISSION PROBE ONLY', (FIXTURE / filename).read_text())
        frame = (ROOT / 'examples/modules/binary-frame/Protocol/Frame.fib').read_text()
        self.assertEqual(re.findall(r'^export\n(\w+) :', frame, re.M), ['echoFrame'])

    def test_counter_only_insertions_are_exhaustive_and_fail_closed(self):
        with self.assertRaises(AssertionError):
            replace_once('x x', 'x', 'y')
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            observe(directory)
            (directory / 'program.c').write_text(
                'static FValue *fibril_expr_0(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }\n'
                'static FValue *fibril_expr_1(FRuntime *r, FEnv *e) { return f_nat_case(r, e, fibril_expr_0, fibril_expr_0, fibril_expr_0); }\n')
            (directory / 'observer.c').write_bytes((ROOT / 'tools/fixtures/lsp-workload-observer.c').read_bytes())
            before = (directory / 'fibril_runtime.c').read_text()
            labels = instrument(directory)
            after = (directory / 'fibril_runtime.c').read_text()
            self.assertEqual(labels['emitted_operations'], {'f_unit': 1, 'f_nat_case': 1})
            self.assertEqual(before.count('enter(r)'), after.count('enter(r)'))
            for define in ('F_MAX_STEPS', 'F_MAX_BYTES', 'F_MAX_DEPTH'):
                self.assertEqual(re.search(r'#define ' + define + r'.*', before)[0],
                                 re.search(r'#define ' + define + r'.*', after)[0])
            self.assertEqual(before.count('force(r,'), after.count('force(r,'))
            self.assertEqual(before.count('abort('), after.count('abort('))
            self.assertEqual(len(re.findall(r'\ballocate\(r,', before)),
                             len(re.findall(r'\ballocate\(r,', after)) - 1)  # macro definition
            self.assertIn('interact_binary', labels['allocation_sites'])

    def test_committed_evidence_totals_provenance_and_blockers(self):
        data = verify_evidence(EVIDENCE, candidate=False)
        self.assertEqual(data['base_commit'], 'afaf00c4c683a0e05c658a12c80a05d8e123201b')
        sanitized = verify_evidence(EVIDENCE.with_name('lsp-cost-audit-sanitized.json'), candidate=False)
        self.assertEqual(len(data['inputs_sha256']), 156)
        for key in ('syntax', 'admission', 'native', 'inputs_sha256',
                    'private_instrumented_sha256', 'instrumentation'):
            self.assertEqual(data[key], sanitized[key], key)
        rows = {row['entry']: row for row in data['syntax']}
        for label, nodes in [('echoFrame', 4341), ('JSON-binary-API', 7467), ('JSON-Read65', 8002),
                             ('typed-transition', 4359), ('FullIdFour', 8467)]:
            self.assertEqual(rows[label]['core_nodes'], nodes)
        self.assertEqual(rows['helper-equalString']['imported_helper_rhs']['nodes'], 31)
        self.assertEqual(rows['helper-orBool']['imported_helper_rhs']['nodes'], 19)
        self.assertEqual(rows['echoFrame']['named_helper_syntax_occurrences']['helper-equalString'], 22)
        self.assertEqual(rows['JSON-binary-API']['named_helper_syntax_occurrences']['helper-equalString'], 2)
        for row in rows.values():
            self.assertEqual(sum(row['categories'].values()), row['core_nodes'])
            self.assertEqual(sum(row['roles'].values()), row['core_nodes'])
            self.assertEqual(min(8193, sum(row['payload_components'].values())), row['payload_estimate'])
        blocker = next(row for row in data['admission'] if row['entry'] == 'FullIdFour')
        self.assertEqual(blocker['returncode'], 1)
        self.assertIn('blocker', blocker['outcome'])
        self.assertEqual(len(data['native']), 4)
        for row in data['native']:
            self.assertEqual(len(bytes.fromhex(row['input_hex'])), 64)
            self.assertTrue(row['baseline_equal'] and row['whole_buffer_scanned'])
            self.assertFalse(row['whole_jsonrpc_decoded'])
            metrics, attr = row['metrics'], row['attribution']
            self.assertEqual(attr['steps']['unmapped_evaluation'], 0)
            self.assertEqual(sum(attr['steps'].values()), metrics['steps'])
            self.assertEqual(sum(value[1] for value in attr['allocations'].values()), metrics['arena_payload'])
            self.assertEqual(sum(attr['values'].values()), attr['allocations']['new_value'][0])
        dense = next(row for row in data['native'] if row['case'] == '64-token-array')
        self.assertEqual((dense['metrics']['steps'], dense['metrics']['arena_payload']), (97768, 2998705))


if __name__ == '__main__':
    unittest.main()
