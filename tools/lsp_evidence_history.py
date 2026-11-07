"""Verify preserved measurements against recording Git blobs, never live sources.

Source archives without the recording objects cannot verify this provenance;
that is an explicit error, not a skipped check or a current-compiler pass.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

from probe_lsp_workload import ROOT, run_process as run_owned_process

WORKLOAD_REVISION = '14bc13eb9a517f41853b25ae5f51ba507a9b42f5'
COST_AUDIT_REVISION = '5ca14f3f4dad4694b049e1fe5167d82e5d462b96'
# The original recording is reachable through the directly merged worker lane.
SOURCE_SHARING_REVISION = '840ba8f30c37eb246912294b5f0eeb2c3332f42f'
REFERENCE_REVISION = 'f3d4a14bf1f9542c968914109673d4fb7557daae'
CANDIDATE_HELPERS = frozenset({
    'tools/lsp_source_sharing.py',
    'tools/probe_lsp_source_sharing.py',
    'tools/test_lsp_source_sharing.py',
})


class ProvenanceUnavailable(RuntimeError):
    """Recording objects are unavailable; historical provenance is unverified."""


def historical_blob(revision, path, *, root=ROOT):
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise ValueError('historical revision must be a full commit ID')
    name = str(path)
    if (not name or PurePosixPath(name).is_absolute() or
            any(part in ('', '.', '..') for part in name.split('/'))):
        raise ValueError('historical path must be repository-relative')
    return git_output(['show', '--no-ext-diff', f'{revision}:{name}'], root=root)


def git_output(arguments, *, root=ROOT):
    if not (Path(root) / '.git').exists():
        raise ProvenanceUnavailable('Historical provenance unverified: source archive has no .git metadata')
    try:
        result = run_owned_process(['git', '--no-pager', '-C', str(root), *arguments], timeout=10)
    except FileNotFoundError as failure:
        raise ProvenanceUnavailable('Historical provenance unverified: Git is unavailable') from failure
    if result.returncode:
        raise ProvenanceUnavailable(
            f'Historical provenance unverified: Git {arguments!r} failed: '
            + result.stderr.decode(errors='replace'))
    return result.stdout


def verify_recording_ancestry(*, root=ROOT):
    """All required snapshots must travel with the imported bootstrap history."""
    for revision in (WORKLOAD_REVISION, COST_AUDIT_REVISION, SOURCE_SHARING_REVISION):
        git_output(['merge-base', '--is-ancestor', revision, REFERENCE_REVISION], root=root)


def source_epoch(path, *, candidate):
    """Baseline recording plus explicitly introduced candidate files; no fallback."""
    if candidate and (path.startswith('tools/fixtures/lsp-source-sharing/') or path in CANDIDATE_HELPERS):
        return SOURCE_SHARING_REVISION
    return COST_AUDIT_REVISION


def verify_digest(path, expected, revision, *, root=ROOT):
    actual = hashlib.sha256(historical_blob(revision, path, root=root)).hexdigest()
    if actual != expected:
        raise AssertionError(f'{revision}:{path}: recorded digest {expected} != Git blob digest {actual}')


def verify_inputs(inputs, *, candidate, root=ROOT):
    for path, expected in inputs.items():
        verify_digest(path, expected, source_epoch(path, candidate=candidate), root=root)


def recorded_evidence(path, revision, *, root=ROOT):
    path = Path(path)
    content = path.read_bytes()
    if content != historical_blob(revision, path.relative_to(root), root=root):
        raise AssertionError(f'{path}: evidence differs from recording commit {revision}')
    return json.loads(content)


def verify_evidence(path, *, candidate, root=ROOT):
    revision = SOURCE_SHARING_REVISION if candidate else COST_AUDIT_REVISION
    data = recorded_evidence(path, revision, root=root)
    verify_inputs(data['inputs_sha256'], candidate=candidate, root=root)
    return data


def verify_workload_evidence(path, *, root=ROOT):
    data = recorded_evidence(path, WORKLOAD_REVISION, root=root)
    for name, digest in data['production_source_sha256'].items():
        verify_digest(name, digest, WORKLOAD_REVISION, root=root)
    return data
