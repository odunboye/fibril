#!/usr/bin/env python3
"""Offline provenance/failure-mode and inventory-checker unit regressions."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import lsp_evidence_history as history
import check_lsp_audit_nat_case as nat_case


class LSPEvidenceHistory(unittest.TestCase):
    def test_explicit_source_epochs_cover_every_candidate_input(self):
        history.verify_recording_ancestry()
        data = json.loads((history.ROOT / 'docs/assets/evidence/lsp-source-sharing.json').read_text())
        epochs = [history.source_epoch(path, candidate=True) for path in data['inputs_sha256']]
        self.assertEqual(epochs.count(history.COST_AUDIT_REVISION), 148)
        self.assertEqual(epochs.count(history.SOURCE_SHARING_REVISION), 19)
        self.assertEqual(history.source_epoch('tools/lsp_source_sharing.py', candidate=False),
                         history.COST_AUDIT_REVISION)
        with mock.patch.object(history, 'git_output', side_effect=history.ProvenanceUnavailable('not an ancestor')):
            with self.assertRaisesRegex(history.ProvenanceUnavailable, 'not an ancestor'):
                history.verify_recording_ancestry()

    def test_git_uses_owned_bounded_byte_capture(self):
        result = subprocess.CompletedProcess([], 0, b'blob\0bytes', b'')
        with mock.patch.object(history, 'run_owned_process', return_value=result) as owned:
            self.assertEqual(history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile'), b'blob\0bytes')
        owned.assert_called_once_with(
            ['git', '--no-pager', '-C', str(history.ROOT), 'show', '--no-ext-diff',
             history.COST_AUDIT_REVISION + ':Makefile'], timeout=10)
        for path in ('/Makefile', '../Makefile', 'src/../Makefile', './Makefile'):
            with self.assertRaises(ValueError):
                history.historical_blob(history.COST_AUDIT_REVISION, path)
        with self.assertRaises(ValueError):
            history.historical_blob('HEAD', 'Makefile')

    def test_source_archive_missing_git_and_missing_objects_are_unverified(self):
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.object(history, 'run_owned_process') as owned:
                with self.assertRaisesRegex(history.ProvenanceUnavailable, 'source archive'):
                    history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile', root=Path(directory))
                owned.assert_not_called()
        with mock.patch.object(history, 'run_owned_process', side_effect=FileNotFoundError):
            with self.assertRaisesRegex(history.ProvenanceUnavailable, 'Git is unavailable'):
                history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile')
        result = subprocess.CompletedProcess([], 128, b'', b'missing object')
        with mock.patch.object(history, 'run_owned_process', return_value=result):
            with self.assertRaisesRegex(history.ProvenanceUnavailable, 'missing object'):
                history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile')

    def test_digest_mismatch_fails_without_revision_fallback(self):
        blob = history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile')
        history.verify_inputs({'Makefile': hashlib.sha256(blob).hexdigest()}, candidate=False)
        with self.assertRaisesRegex(AssertionError, 'Git blob digest'):
            history.verify_inputs({'Makefile': '0' * 64}, candidate=False)
        with mock.patch.object(history, 'historical_blob', return_value=b'wrong epoch') as read:
            with self.assertRaises(AssertionError):
                history.verify_inputs({'tools/lsp_source_sharing.py': '0' * 64}, candidate=True)
            read.assert_called_once_with(history.SOURCE_SHARING_REVISION,
                                         'tools/lsp_source_sharing.py', root=history.ROOT)

    def test_evidence_json_must_remain_byte_identical_to_recording(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'evidence.json'
            original = b'{"inputs_sha256": {}}\n'
            path.write_bytes(original + b'\n')
            with mock.patch.object(history, 'historical_blob', return_value=original):
                with self.assertRaisesRegex(AssertionError, 'evidence differs'):
                    history.verify_evidence(path, candidate=False, root=root)

    def test_nat_case_checker_rejects_missing_fields_roles_and_wrong_counts(self):
        # Checker unit test only. The separate --audit command executes real Idris.
        rows = [dict(tree=nat_case.expected_nat_case(q), core_nodes=18, payload_estimate=0)
                for q in (1, 2)]
        def captured(documents):
            return subprocess.CompletedProcess([], 0,
                b'\n'.join(json.dumps(row).encode() for row in documents), b'')
        with mock.patch.object(nat_case, 'run_process', return_value=captured(rows)):
            self.assertEqual(nat_case.check('/checker-unit-only'), rows)
        mutations = []
        missing = copy.deepcopy(rows); missing[0]['tree']['children'].pop(); mutations.append(missing)
        role = copy.deepcopy(rows)
        role[0]['tree']['children'][3]['children'][1]['children'][1]['role'] = 'unknown_argument'
        mutations.append(role)
        count = copy.deepcopy(rows); count[0]['core_nodes'] = 17; mutations.append(count)
        for changed in mutations:
            with mock.patch.object(nat_case, 'run_process', return_value=captured(changed)):
                with self.assertRaises(AssertionError):
                    nat_case.check('/checker-unit-only')


if __name__ == '__main__':
    unittest.main()
