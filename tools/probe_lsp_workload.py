#!/usr/bin/env python3
"""OFFLINE bounded observations of unchanged source; no cap/loop experiments.

Exit zero means the observations matched baseline policy, not LSP decoding success.
Python JSON is used only as fixture oracle/evidence serialization.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile

from generate_lsp_workload import ROOT, artifacts, bodies, frame
from observe_json_state_sharing import oracle
from test_binary_iteration import observe

FRAME_ROOT = ROOT / 'examples/modules/binary-frame'
JSON_ROOT = ROOT / 'tools/fixtures/json-iteration'
METRICS = ['steps', 'peak_pure_depth', 'arena_payload', 'callbacks', 'reads', 'writes',
           'consumed_bytes', 'accepted_bytes', 'flushes', 'requests', 'reserved_capacity']


def checked(command, timeout=120):
    result = subprocess.run(list(map(str, command)), capture_output=True, timeout=timeout)
    if result.returncode:
        raise AssertionError((command, result.returncode, result.stderr.decode(errors='replace')))
    return result.stdout


def native(exe, directory, root, entry):
    directory.mkdir()
    (directory / 'program.c').write_bytes(checked([exe, 'emit-c-binary', '--source-dir', root, entry]))
    observe(directory)  # Existing profiler: counter insertions only in private copies.
    assert (directory / 'fibril_binary_runtime.c').read_text().count('(iteration_callbacks++, apply_thunk(r, step, input))') == 2
    assert (directory / 'fibril_runtime.c').read_text().count('if(r->depth>iteration_peak)') == 1
    shutil.copyfile(ROOT / 'tools/fixtures/lsp-workload-observer.c', directory / 'observer.c')
    checked(shlex.split(os.environ.get('CC', 'cc')) + ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
        '-I', directory, directory / 'program.c', directory / 'observer.c', '-o', directory / 'native'])
    return directory / 'native'


def observation(command, data, timeout):
    result = subprocess.run(list(map(str, command)), input=data, capture_output=True, timeout=timeout)
    diagnostic = result.stderr.decode('utf-8', errors='strict')
    match = re.search(r'^PROFILE ([\d ]+)\n', diagnostic, re.M)
    metrics = dict(zip(METRICS, map(int, match[1].split()), strict=True)) if match else None
    if match:
        diagnostic = diagnostic.replace(match[0], '')
    if any(word in diagnostic for word in ('Sanitizer', 'runtime error:', 'AddressSanitizer')):
        raise AssertionError(diagnostic)
    return result.returncode, result.stdout, diagnostic, metrics


def run(exe, timeout, measure=None):
    rows = []
    with tempfile.TemporaryDirectory(prefix='fibril-lsp-workload-') as temporary:
        work = Path(temporary)
        entries = [('canonical-frame', FRAME_ROOT, FRAME_ROOT / 'Main.fib'),
                   ('json-read65', JSON_ROOT, JSON_ROOT / 'Read65.fib')]
        admissions = []
        if measure:
            for label, root, entry in entries + [('json-binary-api', JSON_ROOT, JSON_ROOT / 'ParseBinary.fib')]:
                text = checked([measure, root, entry]).decode().strip()
                match = re.fullmatch(r'CORE_NODES=(\d+) PAYLOAD=(\d+)', text)
                if not match:
                    raise AssertionError(text)
                admissions.append({'entry': label, 'core_nodes': int(match[1]), 'literal_payload': int(match[2])})
        for consumer, root, entry in entries:
            checked([exe, 'check', '--source-dir', root, entry])
            executable = native(exe, work / consumer, root, entry)
            inputs = [(name, body, 'lsp-fixture') for name, body, _ in bodies()]
            if consumer == 'json-read65':
                inputs += [('control-tokens64', b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']', 'diagnostic-control'),
                           ('control-string64', b'"' + b'a' * 62 + b'"', 'diagnostic-control'),
                           ('control-utf8-string64', ('"' + 'ÿ' * 31 + '"').encode(), 'diagnostic-control'),
                           ('control-padded64', b' ' * 63 + b'1', 'diagnostic-control')]
            for name, body, shape in inputs:
                data = frame(body) if consumer == 'canonical-frame' else body
                policy_rejection = consumer == 'canonical-frame' and len(body) > 4096
                # Read65 only supplies this prefix to the parser; do not oracle
                # a full larger message as though the reader delivered it.
                expected = frame(body) if consumer == 'canonical-frame' else oracle(body[:65])[2]
                for backend, command in [('hosted', [exe, 'run-binary', '--source-dir', root, entry]),
                                         ('native', [executable])]:
                    code, output, diagnostic, metrics = observation(command, data, timeout)
                    if policy_rejection:
                        assert code != 0 and output == b'' and 'Binary program rejected input' in diagnostic, (name, diagnostic)
                        outcome = 'framer-body-cap-rejection-not-parsing'
                    else:
                        assert code == 0 and diagnostic == '' and output == expected, (name, backend, code, diagnostic)
                        if consumer == 'canonical-frame':
                            outcome = 'opaque-frame-echo-not-json-decoding'
                        elif len(body) > 64:
                            outcome = 'json-diagnostic-cap-denial-not-whole-body-parsing'
                        else:
                            outcome = 'whole-buffer-diagnostic-token-transfer'
                    if backend == 'native':
                        assert metrics is not None
                        consumed = metrics['consumed_bytes']
                        if consumer == 'json-read65':
                            assert consumed == min(65, len(body))
                        elif not policy_rejection:
                            assert consumed == len(data)
                    row = {'consumer': consumer, 'case': name, 'input_shape': shape, 'backend': backend,
                           'body_bytes': len(body), 'supplied_bytes': len(data), 'exit_code': code,
                           'outcome': outcome, 'output_bytes': len(output),
                           'output_sha256': hashlib.sha256(output).hexdigest(),
                           'diagnostic': diagnostic.strip(), 'native_metrics': metrics,
                           'whole_json_body_parsed': consumer == 'json-read65' and len(body) <= 64,
                           'whole_jsonrpc_decoded': False}
                    rows.append(row)
                    print(json.dumps({k: v for k, v in row.items() if k != 'output_sha256'}), flush=True)
    return {'scope': 'bounded baseline observations; no production JSON/LSP or larger-input parser success',
            'source_base': '83aba54c5f03ea309d9fd8515fb9eb3d02daf4f9',
            'compiler': str(exe.relative_to(ROOT)) if exe.is_relative_to(ROOT) else str(exe),
            'compiler_sha256': hashlib.sha256(exe.read_bytes()).hexdigest(),
            'production_source_sha256': {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in (
                'examples/modules/binary-frame/Main.fib', 'examples/modules/binary-frame/Protocol/Frame.fib',
                'tools/fixtures/json-iteration/Read65.fib', 'tools/fixtures/json-iteration/Protocol/JSON.fib',
                'src/Fibril/Driver/Binary.idr', 'runtime/native/fibril_runtime.c',
                'runtime/native/fibril_binary_runtime.c', 'runtime/native/fibril_bytes.c')},
            'cc': os.environ.get('CC', 'cc'), 'timeout_seconds_per_process': timeout,
            'corpus_manifest_sha256': hashlib.sha256(artifacts()['manifest.json']).hexdigest(),
            'hosted_consumption': 'not instrumented; do not attribute supplied bytes as consumed',
            'native_consumption': 'logical adapter bytes; FILE may prefetch; not raw descriptor position',
            'admission': admissions, 'rows': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fibril', type=Path, default=ROOT / 'build/exec/fibril')
    parser.add_argument('--measure', type=Path)
    parser.add_argument('--timeout', type=int, default=90)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    evidence = run(args.fibril.resolve(), args.timeout, args.measure)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2) + '\n')


if __name__ == '__main__':
    main()
