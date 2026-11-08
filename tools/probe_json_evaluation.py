#!/usr/bin/env python3
"""Counter-only JSON dispatch/allocation profile, with plain-observer agreement."""
import argparse
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import tempfile

from probe_composed import ROOT, EXE, digest, required
from probe_lsp_cost_audit import compile_native, execute
from lsp_cost_instrument import instrument
from test_binary_iteration import observe
from observe_json_state_sharing import oracle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    source = ROOT / 'tools/fixtures/json-iteration'
    runtime = ROOT / 'runtime/native'
    inputs = [p for directory in (ROOT / 'src', ROOT / 'stdlib', runtime, source)
              for p in directory.rglob('*') if p.is_file()]
    inputs += [Path(__file__), ROOT / 'tools/lsp_cost_instrument.py',
               ROOT / 'tools/test_binary_iteration.py', ROOT / 'tools/probe_lsp_cost_audit.py',
               ROOT / 'tools/probe_lsp_workload.py', ROOT / 'tools/observe_json_state_sharing.py',
               ROOT / 'tools/fixtures/lsp-workload-observer.c', ROOT / 'pack.toml']
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in sorted(set(inputs))}
    compiler = digest(ROOT / 'build/exec/fibril_app/fibril.so')
    report = {'schema': 'fibril-json-evaluation-v1',
        'scope': 'existing 64-byte diagnostic; full buffer plus EOF; no budget changes',
        'revision': required(['git', 'rev-parse', 'HEAD'], cwd=ROOT),
        'git_status': required(['git', 'status', '--porcelain'], cwd=ROOT),
        'platform': platform.platform(), 'compiler_image_sha256': compiler,
        'cc_version': required(shlex.split(os.environ.get('CC', 'cc')) + ['--version']),
        'inputs_sha256': hashes, 'rows': []}
    emitted = required([EXE, 'emit-c-binary', '--source-dir', source, source / 'Read65.fib']).encode()
    with tempfile.TemporaryDirectory(prefix='fibril-json-profile-') as temporary:
        work = Path(temporary)
        plain, attributed = work / 'plain', work / 'attributed'
        for directory in (plain, attributed):
            directory.mkdir()
            (directory / 'program.c').write_bytes(emitted)
            observe(directory)
            shutil.copyfile(ROOT / 'tools/fixtures/lsp-workload-observer.c', directory / 'observer.c')
        report['instrumentation'] = instrument(attributed)
        report['private_instrumented_sha256'] = {name: digest(attributed / name) for name in
            ('program.c', 'fibril_runtime.c', 'fibril_binary_runtime.c', 'observer.c')}
        compile_native(plain)
        compile_native(attributed)
        cases = {'dense-64': b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']',
                 'ascii-64': b'"' + b'a' * 62 + b'"',
                 'utf8-64': b'"' + 'ÿ'.encode() * 31 + b'"',
                 'padded-64': b' ' * 63 + b'1'}
        for name, data in cases.items():
            expected = oracle(data)[2]
            baseline, metrics, _ = execute([plain / 'native'], data)
            actual, counters, attribution = execute([attributed / 'native'], data)
            assert actual == baseline == expected, name
            assert counters == metrics, name
            assert attribution['steps']['unmapped_evaluation'] == 0, name
            assert sum(attribution['steps'].values()) == metrics['steps'], name
            assert sum(pair[1] for pair in attribution['allocations'].values()) == metrics['arena_payload'], name
            assert sum(attribution['values'].values()) == attribution['allocations']['new_value'][0], name
            report['rows'].append({'case': name, 'input_hex': data.hex(), 'output_hex': actual.hex(),
                                   'metrics': metrics, 'attribution': attribution, 'observer_matches': True})
    assert all(digest(ROOT / name) == checksum for name, checksum in hashes.items())
    assert digest(ROOT / 'build/exec/fibril_app/fibril.so') == compiler
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(args.output)


if __name__ == '__main__':
    main()
