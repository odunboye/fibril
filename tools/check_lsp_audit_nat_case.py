#!/usr/bin/env python3
"""Check current private Audit NatCase/WithRegion inventories, not evidence.

Compile Audit.idr separately against this worktree, then supply --audit PATH.
No compiler/install, protocol matrix, or historical measurement runs here.
"""
import argparse
import json
from pathlib import Path

from probe_lsp_cost_audit import summarize
from probe_lsp_workload import run_process


def node(tag, role='computational', detail=None, children=None):
    return dict(tag=tag, role=role, detail=detail or [], literal=0, nominal=0,
                children=children or [])


def expected_nat_case(quantity):
    nat = lambda: node('NatType', 'metadata')
    return node('NatCase', children=[
        node('Lambda', 'metadata', [0], [nat(), nat()]),
        node('NatSucc', children=[node('NatZero')]),
        node('Apply', children=[node('Lambda', detail=[0], children=[nat(), node('NatZero')]),
                                node('NatZero', 'erased_argument')]),
        node('Lambda', detail=[quantity], children=[nat(),
            node('Apply', children=[
                node('Lambda', detail=[0], children=[nat(), node('Variable', detail=[1])]),
                node('Variable', 'erased_argument', [0])])])])


def check(audit):
    result = run_process([audit, '--nat-case-regression'], timeout=30)
    assert result.returncode == 0 and result.stderr == b'', result
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    assert len(rows) == 2, rows
    for quantity, row in zip((1, 2), rows, strict=True):
        assert row['tree'] == expected_nat_case(quantity), row
        # summarize counts actual dumped descendants and compares coreNodes.
        summary = summarize(row)
        assert summary['core_nodes'] == 18, summary
        assert summary['categories']['NatCase'] == 1, summary
        assert 'unknown_argument' not in summary['roles'], summary
    return rows


def expected_with_region():
    nat = lambda: node('NatType', 'metadata')
    return node('Lambda', detail=[2], children=[nat(),
        node('WithRegion', children=[nat(),
            node('Lambda', detail=[0], children=[node('Universe', 'metadata', [0]),
                node('Apply', children=[
                    node('Lambda', detail=[0], children=[nat(), node('Variable', detail=[2])]),
                    node('Variable', 'erased_argument', [1])])])])])


def check_with_region(audit):
    result = run_process([audit, '--with-region-regression'], timeout=30)
    assert result.returncode == 0 and result.stderr == b'', result
    rows = [json.loads(line) for line in result.stdout.splitlines()]
    assert len(rows) == 1, rows
    row = rows[0]
    assert row['tree'] == expected_with_region(), row
    summary = summarize(row)
    assert summary['core_nodes'] == 11, summary
    assert summary['categories']['WithRegion'] == 1, summary
    assert 'unknown_argument' not in summary['roles'], summary
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', required=True, type=Path)
    args = parser.parse_args()
    check(args.audit.resolve())
    print('PASS NatCase four fields, Linear/Unrestricted Lambda contexts, erased applications, coreNodes=18')
    check_with_region(args.audit.resolve())
    print('PASS WithRegion two nonbinding fields, metadata result, body Lambda context, coreNodes=11')


if __name__ == '__main__':
    main()
