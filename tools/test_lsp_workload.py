#!/usr/bin/env python3
"""OFFLINE corpus/evidence checks; recorded cap denials are not parser passes."""
import hashlib
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import patch

from generate_lsp_workload import (DESTINATION, ROOT, SOURCE, ObjectMembers, artifacts,
                                   bodies, describe, frame)
from observe_json_state_sharing import oracle
from probe_lsp_workload import observation


class LSPWorkload(unittest.TestCase):
    def test_committed_corpus_is_exact_and_reproducible(self):
        expected = artifacts()
        actual = {p.name: p.read_bytes() for p in DESTINATION.iterdir() if p.is_file()}
        self.assertEqual(actual, expected)
        self.assertEqual(artifacts(), expected)
        self.assertEqual(len(list(bodies())), 14)
        for name, body, provenance in bodies():
            with self.subTest(case=name):
                self.assertEqual(actual[name + '.frame'], frame(body))
                header, payload = actual[name + '.frame'].split(b'\r\n\r\n', 1)
                self.assertEqual(header, b'Content-Length: ' + str(len(payload)).encode())
                self.assertEqual(payload, body)
                self.assertFalse(describe(name, body, provenance)['captured_client_traffic'])

    def test_duplicate_fields_and_id_kinds_remain_ordered(self):
        rows = {r['name']: r for r in json.loads(artifacts()['manifest.json'])['cases']}
        duplicate = rows['duplicate-fields']
        self.assertEqual(duplicate['expected_id_kinds'], ['string', 'number'])
        self.assertEqual(duplicate['expected_id_values'], ['s-1', 7])
        self.assertEqual(duplicate['expected_fields']['object_members'][-1],
                         ['params', {'object_members': [['x', 1], ['x', 2]]}])
        self.assertEqual(duplicate['envelope_policy'], 'ambiguous-duplicate-id-no-dispatch-expectation')
        self.assertEqual(rows['initialized']['expected_id_kinds'], ['absent'])
        self.assertEqual(rows['shutdown']['expected_id_kinds'], ['number'])
        self.assertEqual(rows['shutdown-string-id']['expected_id_kinds'], ['string'])
        for invalid in (b'{"x":"\\ud800","x":0}', b'{"x":0,"x":{"y":"\\ud800"}}'):
            with self.assertRaises(UnicodeError):
                describe('invalid', invalid, 'synthetic')
        with self.assertRaises(ValueError):
            describe('invalid', b'{"x":}', 'synthetic')

    def test_ordered_utf16_edits_nonascii_and_crlf(self):
        body = dict((name, data) for name, data, _ in bodies())['didChange-utf16']
        changes = json.loads(body)['params']['contentChanges']
        text = SOURCE
        for change in changes:
            span = change['range']
            self.assertEqual(span['start']['line'], span['end']['line'])
            lines = text.splitlines(keepends=True)
            index = span['start']['line']
            raw = lines[index].encode('utf-16-le')
            start, end = 2 * span['start']['character'], 2 * span['end']['character']
            # Strict decode ensures no edit splits a surrogate pair.
            replaced = raw[start:end].decode('utf-16-le')
            self.assertEqual(len(replaced.encode('utf-16-le')) // 2, change['rangeLength'])
            lines[index] = (raw[:start].decode('utf-16-le') + change['text'] + raw[end:].decode('utf-16-le'))
            text = ''.join(lines)
        self.assertEqual(text, 'main : IO Unit\r\nmain = putStrLn "α🧵λé"\r\n')
        self.assertGreater(len(body), len(body.decode()))

    def test_boundaries_tokens_nesting_and_realistic_capabilities(self):
        rows = {r['name']: r for r in json.loads(artifacts()['manifest.json'])['cases']}
        for n in (4095, 4096, 4097):
            row = rows[f'didOpen-boundary-{n}']
            self.assertEqual(row['body_bytes'], n)
            self.assertEqual(row['wire_bytes'], n + 24)
            self.assertEqual(row['canonical_framer_policy'], 'within-4096-body-cap' if n <= 4096 else 'over-4096-body-cap')
        capabilities = rows['initialize-capabilities']
        self.assertEqual((capabilities['body_bytes'], capabilities['tokens'], capabilities['max_container_nesting']), (3681, 720, 8))
        self.assertGreater(capabilities['tokens'], 512)  # Not silently an accepted policy.
        self.assertGreater(rows['didOpen-large']['body_bytes'], 4096)
        self.assertGreater(rows['didChange-large']['body_bytes'], 4096)
        duplicate = json.loads(dict((n, b) for n, b, _ in bodies())['duplicate-fields'], object_pairs_hook=ObjectMembers)
        self.assertEqual([item for key, item in duplicate if key == 'id'], ['s-1', 7])

    def test_committed_evidence_accounting_and_oracle(self):
        evidence = json.loads((ROOT / 'docs/assets/evidence/lsp-workload.json').read_text())
        self.assertEqual(evidence['corpus_manifest_sha256'], hashlib.sha256(artifacts()['manifest.json']).hexdigest())
        self.assertEqual(len(evidence['production_source_sha256']), 8)
        for path, digest in evidence['production_source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), digest, path)
        inputs = {name: body for name, body, _ in bodies()}
        inputs.update({'control-tokens64': b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']',
                       'control-string64': b'"' + b'a' * 62 + b'"',
                       'control-utf8-string64': ('"' + 'ÿ' * 31 + '"').encode(),
                       'control-padded64': b' ' * 63 + b'1'})
        self.assertEqual(len(evidence['rows']), 64)
        self.assertEqual(len({(r['consumer'], r['case'], r['backend']) for r in evidence['rows']}), 64)
        for row in evidence['rows']:
            body = inputs[row['case']]
            native = row['native_metrics']
            self.assertFalse(row['whole_jsonrpc_decoded'])
            if row['consumer'] == 'canonical-frame':
                self.assertFalse(row['whole_json_body_parsed'])
                accepted = len(body) <= 4096
                output = frame(body) if accepted else b''
                self.assertEqual(row['exit_code'], 0 if accepted else 1)
                if native:
                    self.assertEqual(native['consumed_bytes'], len(frame(body)) if accepted else 20)
                    self.assertEqual(native['reserved_capacity'], 2 * len(frame(body)) if accepted else 20)
                    self.assertEqual(native['flushes'], 2 if accepted else 0)
            else:
                output = oracle(body[:65])[2]
                self.assertEqual(row['exit_code'], 0)
                self.assertEqual(row['whole_json_body_parsed'], len(body) <= 64)
                if native:
                    self.assertEqual(native['consumed_bytes'], min(len(body), 65))
                    self.assertEqual(native['callbacks'], len(body) + 1 if len(body) <= 64 else 0)
                    self.assertEqual(native['reserved_capacity'], 65 + len(output))
                    self.assertEqual(native['requests'], 2)
                if len(body) > 64:
                    self.assertEqual(row['outcome'], 'json-diagnostic-cap-denial-not-whole-body-parsing')
            self.assertEqual(row['output_bytes'], len(output))
            self.assertEqual(row['output_sha256'], hashlib.sha256(output).hexdigest())
            if native:
                self.assertEqual(native['accepted_bytes'], len(output))
                self.assertLess(native['steps'], 100000)
                self.assertLess(native['arena_payload'], 16 * 1024 * 1024)
            else:
                self.assertEqual(row['backend'], 'hosted')
        self.assertEqual([r['core_nodes'] for r in evidence['admission']], [4341, 8002, 7467])

    def test_normal_and_sanitized_evidence_agree(self):
        normal = json.loads((ROOT / 'docs/assets/evidence/lsp-workload.json').read_text())
        sanitized = json.loads((ROOT / 'docs/assets/evidence/lsp-workload-sanitized.json').read_text())
        self.assertIn('-fsanitize=address,undefined', sanitized['cc'])
        self.assertEqual(normal['rows'], sanitized['rows'])
        self.assertEqual(normal['admission'], sanitized['admission'])
        self.assertEqual(normal['corpus_manifest_sha256'], sanitized['corpus_manifest_sha256'])
        self.assertEqual(normal['production_source_sha256'], sanitized['production_source_sha256'])
        self.assertEqual(normal['compiler_sha256'], sanitized['compiler_sha256'])

    def test_observer_metrics_sanitizer_and_timeout_fail_closed(self):
        result = subprocess.CompletedProcess([], 0, b'ok', b'PROFILE 1 2 3 4 5 6 7 8 9 10 11\n')
        with patch('probe_lsp_workload.subprocess.run', return_value=result):
            code, output, diagnostic, metrics = observation(['unused'], b'', 1)
            self.assertEqual((code, output, diagnostic), (0, b'ok', ''))
            self.assertEqual(metrics['consumed_bytes'], 7)
            self.assertEqual(metrics['reserved_capacity'], 11)
        with patch('probe_lsp_workload.subprocess.run', side_effect=subprocess.TimeoutExpired('unused', 1)):
            with self.assertRaises(subprocess.TimeoutExpired):
                observation(['unused'], b'', 1)
        result.stderr = b'runtime error: invalid memory access\n'
        with patch('probe_lsp_workload.subprocess.run', return_value=result):
            with self.assertRaises(AssertionError):
                observation(['unused'], b'', 1)


if __name__ == '__main__':
    unittest.main()
