#!/usr/bin/env python3
"""Historical provenance checks for the consolidated Python/Fibril LSP lanes."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import lsp_evidence_history as history


class LSPEvidenceHistory(unittest.TestCase):
    def test_epochs_are_reachable_and_cover_candidate_inputs(self):
        history.verify_recording_ancestry()
        data = json.loads((history.ROOT / 'docs/assets/evidence/lsp-source-sharing.json').read_text())
        epochs = [history.source_epoch(p, candidate=True) for p in data['inputs_sha256']]
        self.assertEqual(epochs.count(history.COST_AUDIT_REVISION), 148)
        self.assertEqual(epochs.count(history.SOURCE_SHARING_REVISION), 19)
        with mock.patch.object(history, 'git_output', side_effect=history.ProvenanceUnavailable('not ancestor')):
            with self.assertRaises(history.ProvenanceUnavailable):
                history.verify_recording_ancestry()

    def test_owned_capture_and_argument_validation(self):
        result = subprocess.CompletedProcess([], 0, b'blob\0bytes', b'')
        with mock.patch.object(history, 'run_owned_process', return_value=result) as owned:
            self.assertEqual(history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile'), b'blob\0bytes')
        owned.assert_called_once_with(['git', '--no-pager', '-C', str(history.ROOT), 'show',
            '--no-ext-diff', history.COST_AUDIT_REVISION + ':Makefile'], timeout=10)
        for path in ('/Makefile', '../Makefile', 'src/../Makefile', './Makefile'):
            with self.assertRaises(ValueError):
                history.historical_blob(history.COST_AUDIT_REVISION, path)
        with self.assertRaises(ValueError):
            history.historical_blob('HEAD', 'Makefile')

    def test_unavailable_history_fails_explicitly(self):
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.object(history, 'run_owned_process') as owned:
                with self.assertRaisesRegex(history.ProvenanceUnavailable, 'source archive'):
                    history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile', root=Path(directory))
                owned.assert_not_called()
        with mock.patch.object(history, 'run_owned_process', side_effect=FileNotFoundError):
            with self.assertRaisesRegex(history.ProvenanceUnavailable, 'Git is unavailable'):
                history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile')
        with mock.patch.object(history, 'run_owned_process', return_value=subprocess.CompletedProcess([], 128, b'', b'missing object')):
            with self.assertRaisesRegex(history.ProvenanceUnavailable, 'missing object'):
                history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile')

    def test_digest_mismatch_has_no_revision_fallback(self):
        blob = history.historical_blob(history.COST_AUDIT_REVISION, 'Makefile')
        history.verify_inputs({'Makefile': hashlib.sha256(blob).hexdigest()}, candidate=False)
        with self.assertRaisesRegex(AssertionError, 'Git blob digest'):
            history.verify_inputs({'Makefile': '0' * 64}, candidate=False)
        with mock.patch.object(history, 'historical_blob', return_value=b'wrong epoch') as read:
            with self.assertRaises(AssertionError):
                history.verify_inputs({'tools/lsp_source_sharing.py': '0' * 64}, candidate=True)
            read.assert_called_once_with(history.SOURCE_SHARING_REVISION, 'tools/lsp_source_sharing.py', root=history.ROOT)

    def test_recorded_evidence_bytes_cannot_change(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'evidence.json'
            original = b'{"inputs_sha256": {}}\n'
            path.write_bytes(original + b'\n')
            with mock.patch.object(history, 'historical_blob', return_value=original):
                with self.assertRaisesRegex(AssertionError, 'evidence differs'):
                    history.verify_evidence(path, candidate=False, root=root)


if __name__ == '__main__':
    unittest.main()
