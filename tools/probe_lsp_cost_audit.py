#!/usr/bin/env python3
"""OFFLINE syntax/admission audit and counter-only existing 64-byte executions.

All subprocesses use the owned-anchor whole-buffer+EOF helper. No larger parser
cap/loop, live input, production runtime edit or admission-policy experiment.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
import os
import platform
import sys
from pathlib import Path
import re
import shlex
import shutil
import tempfile

from probe_lsp_workload import ROOT, METRICS, checked, run_process
from test_binary_iteration import observe
from observe_json_state_sharing import oracle
from lsp_cost_instrument import instrument

FIXTURE = ROOT / 'tools/fixtures/lsp-cost-audit'
EXE = ROOT / 'build/exec/fibril'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def syntax_hash(tag, detail, children):
    return hashlib.sha256(json.dumps([tag, detail, children], separators=(',', ':')).encode()).hexdigest()


def syntax_identity(node):
    children = [syntax_identity(child) for child in node['children']]
    return (1 + sum(child[0] for child in children),
            syntax_hash(node['tag'], node.get('detail', []), [child[1] for child in children]))


def summarize(document, named_helpers=None):
    if document.get('representation') == 'bounded-global-expansion':
        raise ValueError('Legacy expanded-tree cost/admission probing cannot measure shared-graph admission; migrate the probe schema before collecting new evidence')
    """Disjoint ancestor-dominant roles; all list cells counted like coreNodes.

    Shape fingerprints deliberately omit variable indices, names, literals and
    quantities: candidates for inspection ONLY, never safe CSE or node savings.
    """
    categories, roles, role_categories = Counter(), Counter(), defaultdict(Counter)
    payload = Counter()
    shapes, syntax = defaultdict(list), defaultdict(list)
    syntax_occurrences = Counter()

    def visit(node, inherited='computational'):
        role = node['role'] if inherited == 'computational' else inherited
        tag = node['tag']
        categories[tag] += 1
        roles[role] += 1
        role_categories[role][tag] += 1
        payload['literal'] += node['literal']
        payload['nominal'] += node['nominal']
        children = [visit(child, role) for child in node['children']]
        size = 1 + sum(child[0] for child in children)
        shape = hashlib.sha256((tag + '(' + ','.join(child[1] for child in children) + ')').encode()).hexdigest()
        exact = syntax_hash(tag, node.get('detail', []), [child[2] for child in children])
        syntax_occurrences[exact] += 1
        if size >= 20:
            shapes[shape].append((size, tag, role))
            syntax[exact].append((size, tag, role))
        return size, shape, exact

    size, _, _ = visit(document['tree'])
    assert size == document['core_nodes'] == sum(categories.values()) == sum(roles.values())
    assert min(8193, sum(payload.values())) == document['payload_estimate']
    repeated = sorted((dict(shape_sha256=key, nodes=rows[0][0], root=rows[0][1],
                            occurrences=len(rows), roles=dict(Counter(row[2] for row in rows)))
                       for key, rows in shapes.items() if len(rows) > 1),
                      key=lambda row: (row['nodes'] * (row['occurrences'] - 1), row['shape_sha256']), reverse=True)[:10]
    repeated_syntax = sorted((dict(syntax_sha256=key, nodes=rows[0][0], root=rows[0][1],
                                   occurrences=len(rows), roles=dict(Counter(row[2] for row in rows)))
                              for key, rows in syntax.items() if len(rows) > 1),
                             key=lambda row: (row['nodes'] * (row['occurrences'] - 1), row['syntax_sha256']), reverse=True)[:10]
    return dict(core_nodes=size, payload_estimate=document['payload_estimate'], payload_components=dict(payload),
                categories=dict(categories), roles=dict(roles),
                role_categories={key: dict(value) for key, value in role_categories.items()},
                repeated_shapes_not_dedup_savings=repeated,
                repeated_syntax_not_dedup_savings=repeated_syntax,
                named_helper_syntax_occurrences={name: syntax_occurrences[helper['syntax_sha256']]
                                                 for name, helper in (named_helpers or {}).items()})


def prepare_root(work):
    root = work / 'source'
    root.mkdir()
    for origin in (ROOT / 'examples/modules/binary-frame', ROOT / 'tools/fixtures/json-iteration',
                   ROOT / 'tools/fixtures/lsp-lifecycle'):
        for path in origin.rglob('*.fib'):
            if path.parent == origin and path.name not in ('LSP.fib', 'Observation.fib', 'ControlObservation.fib'):
                continue
            target = root / path.relative_to(origin)
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                assert target.read_bytes() == path.read_bytes(), target
            else:
                shutil.copyfile(path, target)
    for path in FIXTURE.glob('*.fib'):
        shutil.copyfile(path, root / path.name)
    return root


def compile_native(directory):
    checked(shlex.split(os.environ.get('CC', 'cc')) +
            ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-I', directory,
             directory / 'program.c', directory / 'observer.c', '-o', directory / 'native'])


def execute(command, data):
    result = run_process(command, input=data, timeout=90)
    assert result.returncode == 0, (command, result.returncode, result.stderr)
    diagnostic = result.stderr.decode('utf-8', errors='strict')
    match = re.search(r'^PROFILE ([\d ]+)\n', diagnostic, re.M)
    assert match, diagnostic
    metrics = dict(zip(METRICS, map(int, match[1].split()), strict=True))
    attr = re.search(r'^ATTR (.+)$', diagnostic, re.M)
    # No unknown warnings or sanitizer diagnostics are accepted.
    assert re.sub(r'^(PROFILE [\d ]+|ATTR .+)\n', '', diagnostic, flags=re.M) == '', diagnostic
    return result.stdout, metrics, json.loads(attr[1]) if attr else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    assert args.audit.is_file() and EXE.is_file()
    evidence = {'scope': 'OFFLINE audit; admission probes are NOT wire composition',
                'base_commit': 'afaf00c4c683a0e05c658a12c80a05d8e123201b',
                'execution_input_contract': 'complete buffer + EOF, not live stdin',
                'compiler_launcher_sha256': digest(EXE),
                'compiler_image_sha256': digest(ROOT / 'build/exec/fibril_app/fibril.so'),
                'audit_launcher_sha256': digest(args.audit),
                'audit_image_sha256': digest(args.audit.parent / 'audit_app/audit.so'),
                'idris2': os.environ.get('IDRIS2'), 'cc': os.environ.get('CC', 'cc'),
                'platform': platform.platform(), 'python': sys.version,
                'idris2_version': checked([os.environ['IDRIS2'], '--version']).decode().strip(),
                'idris2_launcher_sha256': digest(os.environ['IDRIS2']),
                'cc_version': checked(shlex.split(os.environ.get('CC', 'cc')) + ['--version']).decode().strip(),
                'syntax': [], 'admission': [], 'native': []}
    inputs = [p for root in ('src', 'stdlib', 'runtime/native', 'examples/modules/binary-frame',
                            'tools/fixtures/json-iteration', 'tools/fixtures/lsp-lifecycle',
                            'tools/fixtures/lsp-cost-audit')
              for p in (ROOT / root).rglob('*') if p.is_file()]
    inputs += [ROOT / name for name in ('fibril.ipkg', 'Makefile', 'tools/probe_lsp_cost_audit.py',
               'tools/lsp_cost_instrument.py', 'tools/test_lsp_cost_audit.py',
               'tools/probe_lsp_workload.py', 'tools/test_binary_iteration.py',
               'tools/observe_json_state_sharing.py', 'tools/fixtures/lsp-workload-observer.c')]
    evidence['inputs_sha256'] = {str(path.relative_to(ROOT)): digest(path) for path in sorted(set(inputs))}
    with tempfile.TemporaryDirectory(prefix='fibril-lsp-cost-') as temporary:
        work = Path(temporary)
        root = prepare_root(work)
        named_helpers = {}
        entries = [(name, root, filename, False) for name, filename in
                   [('helper-equalString', 'EqualString.fib'), ('helper-orBool', 'OrBool.fib')]] + [
            ('echoFrame', ROOT / 'examples/modules/binary-frame', 'Main.fib', False),
            ('JSON-binary-API', ROOT / 'tools/fixtures/json-iteration', 'ParseBinary.fib', False),
            ('JSON-Read65', ROOT / 'tools/fixtures/json-iteration', 'Read65.fib', True),
            ('typed-transition', ROOT / 'tools/fixtures/lsp-lifecycle', 'Transition.fib', False),
            ('typed-no-output', ROOT / 'tools/fixtures/lsp-lifecycle', 'NoOutput.fib', True),
        ] + [(name, root, name + '.fib', True) for name in
             ('FullIdFour', 'EchoThenTyped', 'JSONThenTyped', 'EchoJSONThenTyped')]
        for label, source_root, filename, emit in entries:
            path = source_root / filename
            source_check = run_process([EXE, 'check', '--source-dir', source_root, path], timeout=120)
            if source_check.returncode:
                diagnostic = source_check.stderr.decode()
                assert source_check.returncode == 1 and 'Expanded core construction budget exhausted (200000)' in diagnostic, (label, source_check)
                assert label in ('JSONThenTyped', 'EchoJSONThenTyped'), label
                evidence['admission'].append(dict(entry=label,
                    outcome='source-construction-blocker; NO closed checked core or native execution',
                    returncode=source_check.returncode, core_nodes=None,
                    stderr=diagnostic.replace(str(source_root.resolve()), '<probe-source>')))
                continue
            tree_bytes = checked([args.audit, source_root, path])
            document = json.loads(tree_bytes)
            row = summarize(document, named_helpers)
            if label.startswith('helper-'):
                # For these two explicit main = helper entries only: the module
                # main-binding wrapper is Apply (Lambda ... Variable 0) rhs.
                tree = document['tree']
                assert tree['tag'] == 'Apply' and len(tree['children']) == 2
                assert tree['children'][0]['tag'] == 'Lambda'
                helper_nodes, helper_hash = syntax_identity(tree['children'][1])
                named_helpers[label] = dict(nodes=helper_nodes, syntax_sha256=helper_hash)
                row['imported_helper_rhs'] = named_helpers[label]
            row.update(entry=label, expanded_inventory_sha256=hashlib.sha256(tree_bytes).hexdigest())
            evidence['syntax'].append(row)
            if emit:
                result = run_process([EXE, 'emit-c-binary', '--source-dir', source_root, path], timeout=120)
                text = result.stderr.decode()
                if result.returncode:
                    assert result.returncode == 1 and 'Native core admission exceeds 8192 nodes' in text, (label, result)
                    assert row['core_nodes'] > 8192
                    outcome = 'source-check-accepted/native-admission-blocker'
                else:
                    assert row['core_nodes'] <= 8192 and result.stdout.startswith(b'/* Generated')
                    outcome = 'source-check-accepted/native-emission-accepted; NOT execution'
                evidence['admission'].append(dict(entry=label, outcome=outcome,
                    returncode=result.returncode, stderr=text, core_nodes=row['core_nodes']))

        # Existing reader and cap/allowance, with genuine complete 64-byte scans.
        baseline, attributed = work / 'baseline', work / 'attributed'
        baseline.mkdir(); attributed.mkdir()
        emitted = checked([EXE, 'emit-c-binary', '--source-dir', ROOT / 'tools/fixtures/json-iteration',
                           ROOT / 'tools/fixtures/json-iteration/Read65.fib'])
        for directory in (baseline, attributed):
            (directory / 'program.c').write_bytes(emitted)
            observe(directory)
            shutil.copyfile(ROOT / 'tools/fixtures/lsp-workload-observer.c', directory / 'observer.c')
        evidence['instrumentation'] = instrument(attributed)
        evidence['private_instrumented_sha256'] = {name: digest(attributed / name) for name in
            ('program.c', 'fibril_runtime.c', 'fibril_binary_runtime.c', 'observer.c')}
        compile_native(baseline); compile_native(attributed)
        cases = {'64-token-array': b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']',
                 'ASCII-string': b'"' + b'a' * 62 + b'"',
                 'UTF8-string': b'"' + 'ÿ'.encode() * 31 + b'"',
                 'whitespace-value': b' ' * 63 + b'1'}
        for label, data in cases.items():
            assert len(data) == 64
            valid_json, scalar_valid, expected = oracle(data)
            assert valid_json and scalar_valid
            plain, metrics, _ = execute([baseline / 'native'], data)
            actual, attributed_metrics, counters = execute([attributed / 'native'], data)
            assert actual == plain == expected, (label, actual, expected)
            assert attributed_metrics == metrics
            assert metrics['consumed_bytes'] == 64 and metrics['callbacks'] == 65
            assert counters['steps']['unmapped_evaluation'] == 0
            assert sum(counters['steps'].values()) == metrics['steps']
            assert sum(value[1] for value in counters['allocations'].values()) == metrics['arena_payload']
            assert sum(counters['values'].values()) == counters['allocations']['new_value'][0]
            evidence['native'].append(dict(case=label, input_hex=data.hex(), output_hex=actual.hex(),
                                            metrics=metrics, attribution=counters,
                                            baseline_equal=True, whole_buffer_scanned=True,
                                            whole_jsonrpc_decoded=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True) + '\n')
    print(f"{len(evidence['syntax'])} syntax entries, {len(evidence['admission'])} admission-only rows, "
          f"{len(evidence['native'])} complete 64-byte native profiles: {args.output}")


if __name__ == '__main__':
    main()
