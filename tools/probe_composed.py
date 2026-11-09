#!/usr/bin/env python3
"""Offline shared-graph measurements; no admission, evaluator or budget changes.

Run after make build. Each timing sample is a fresh process, with no warmup.
Native instrumentation is counter-only, in private copies, checked against plain C.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

from probe_lsp_workload import run_process
from probe_lsp_cost_audit import prepare_root
from observe_json_state_sharing import oracle

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / 'build/exec/fibril'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError(f'instrumentation anchor changed: {old}')
    return source.replace(old, new)


def instrument(directory):
    """Successful payload allocations by caller; no extra evaluation/forcing."""
    path = directory / 'fibril_runtime.c'
    source = path.read_text()
    sites = set()
    current = None
    for line in (source + '\n' + (directory / 'fibril_binary_runtime.c').read_text()).splitlines():
        match = re.match(r'(?:static )?[\w *]+\b(\w+)\([^;]*\) \{', line)
        if match:
            current = match[1]
        if 'allocate(r,' in line:
            if current is None:
                raise ValueError('unidentified allocation site')
            sites.add(current)
    sites = sorted(sites)
    declarations = (f'static size_t measured_count[{len(sites)}], measured_bytes[{len(sites)}];\n'
                    'static size_t measured_peak_bytes, measured_depth, measured_globals, measured_total_bytes;\n')
    source = replace_once(source, 'static void *allocate(FRuntime *r, size_t size) {\n  if (r->error) return NULL;\n  if (size > SIZE_MAX',
        declarations + 'static void *measured_allocate(FRuntime *r, size_t size, const char *site) {\n  if (r->error) return NULL;\n  if (size > SIZE_MAX')
    counters = '  measured_total_bytes += size;\n  if (r->bytes > measured_peak_bytes) measured_peak_bytes = r->bytes;\n'
    for index, site in enumerate(sites):
        counters += f'  if (!strcmp(site, "{site}")) {{ measured_count[{index}]++; measured_bytes[{index}] += size; }}\n'
    source = replace_once(source, '  return (void *)(p + 1);\n}', counters +
        '  return (void *)(p + 1);\n}\n#define allocate(r, size) measured_allocate(r, size, __func__)')
    source = replace_once(source, '  r->steps++; r->depth++; return 1;',
        '  r->steps++; r->depth++; if (r->depth > measured_depth) measured_depth = r->depth; return 1;')
    source = replace_once(source, '  return evaluate(r, body, NULL);',
        '  measured_globals++; return evaluate(r, body, NULL);')
    report = ('\nstatic void measured_report(FRuntime *r) {\n'
        '  fprintf(stderr, "COMPOSED {\\\"steps\\\":%zu,\\\"peak_depth\\\":%zu,\\\"peak_arena_payload\\\":%zu,\\\"final_arena_payload\\\":%zu,\\\"global_calls\\\":%zu,\\\"allocated_payload\\\":%zu,\\\"allocations\\\":{", '
        'r->steps, measured_depth, measured_peak_bytes, r->bytes, measured_globals, measured_total_bytes);\n')
    for index, site in enumerate(sites):
        report += f'  fprintf(stderr, "{"," if index else ""}\\\"{site}\\\":[%zu,%zu]", measured_count[{index}], measured_bytes[{index}]);\n'
    report += '  fprintf(stderr, "}}\\n");\n}\n'
    source = replace_once(source, 'static FValue *evaluate(FRuntime *r, FEval code, FEnv *env) {',
        report + 'static FValue *evaluate(FRuntime *r, FEval code, FEnv *env) {')
    # Console cleanup is last in this file. Leave interactive/resource runners alone.
    anchor = '  while (r.allocations) { FAllocation *next = r.allocations->next; free(r.allocations); r.allocations = next; }'
    offset = source.rindex(anchor)
    source = source[:offset] + '  measured_report(&r);\n' + source[offset:]
    path.write_text(source)
    binary = directory / 'fibril_binary_runtime.c'
    binary.write_text(replace_once(binary.read_text(),
        'static int binary_finish(FRuntime *r, FBinaryContext *context, FByteStatus status) {',
        'static int binary_finish(FRuntime *r, FBinaryContext *context, FByteStatus status) {\n  measured_report(r);'))
    return sites


def timed(command, data=b'', timeout=120):
    """Wall duration includes process startup; RSS is per-command, never RUSAGE_CHILDREN."""
    system = platform.system()
    if system not in ('Darwin', 'Linux') or not Path('/usr/bin/time').is_file():
        raise RuntimeError('RSS collection requires macOS or GNU /usr/bin/time')
    with tempfile.TemporaryDirectory(prefix='fibril-time-') as temporary:
        report = Path(temporary) / 'time.txt'
        flags = ['-l'] if system == 'Darwin' else ['-v']
        start = time.monotonic()
        try:
            result = run_process(['/usr/bin/time', *flags, '-o', report, *map(str, command)],
                                 input=data, timeout=timeout)
        except subprocess.TimeoutExpired:
            return {'outcome': 'timeout', 'wall_seconds': time.monotonic() - start,
                    'peak_rss_bytes': None, 'returncode': None, 'stdout_hex': '',
                    'stderr': 'whole process group deadline exceeded; no result claimed'}
        elapsed = time.monotonic() - start
        text = report.read_text()
        pattern = (r'^\s*(\d+)\s+maximum resident set size' if system == 'Darwin' else
                   r'Maximum resident set size \(kbytes\):\s*(\d+)')
        match = re.search(pattern, text, re.M)
        if not match:
            raise ValueError(f'RSS not available: {text}')
        rss = int(match[1]) * (1 if system == 'Darwin' else 1024)
        return {'outcome': 'success' if result.returncode == 0 else 'rejected',
                'wall_seconds': elapsed, 'peak_rss_bytes': rss,
                'returncode': result.returncode, 'stdout_hex': result.stdout.hex(),
                'stderr': result.stderr.decode('utf-8', errors='strict')}


def samples(command, count, data=b'', timeout=120):
    rows = [timed(command, data, timeout) for _ in range(count)]
    return {'samples': rows, 'median_wall_seconds': statistics.median(r['wall_seconds'] for r in rows),
            'median_peak_rss_bytes': statistics.median(r['peak_rss_bytes'] for r in rows)
                if all(r['peak_rss_bytes'] is not None for r in rows) else None}


def required(command, **kwargs):
    result = subprocess.run(list(map(str, command)), capture_output=True, timeout=300, **kwargs)
    if result.returncode:
        raise RuntimeError((command, result.stdout.decode(errors='replace'), result.stderr.decode(errors='replace')))
    return result.stdout.decode().strip()


def pinned_compiler():
    configured = shlex.split(os.environ.get('IDRIS2', 'idris2'))
    if configured != ['idris2']:
        return configured
    pack = shlex.split(os.environ.get('PACK', 'pack'))
    paths = [line for line in required(pack + ['--log-level=silence', 'app-path', 'idris2'], cwd=ROOT).splitlines()
             if line.startswith('/')]
    if len(paths) != 1:
        raise ValueError(('ambiguous pinned compiler path', paths))
    return paths


def build_measure(work, compiler):
    env = os.environ.copy()
    pack = shlex.split(env.get('PACK', 'pack'))
    for key, flag in [('IDRIS2_PACKAGE_PATH', 'package-path'), ('IDRIS2_LIBS', 'libs-path'), ('IDRIS2_DATA', 'data-path')]:
        paths = [line for line in required(pack + ['--log-level=silence', flag], cwd=ROOT).splitlines() if line.startswith('/')]
        if len(paths) != 1:
            raise ValueError(('ambiguous curated paths', flag, paths))
        env[key] = paths[0]
    external = [p for p in env['IDRIS2_PACKAGE_PATH'].split(os.pathsep) if Path(p).parent.parent.name != 'fibril']
    stage = ROOT / 'build/composed-prefix'
    if stage.is_symlink() or not stage.resolve().is_relative_to(ROOT):
        raise ValueError('unsafe private prefix')
    env['IDRIS2_PREFIX'] = str(stage)
    env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join(external)
    installed = Path(required(compiler + ['--dump-installdir', 'fibril.ipkg'], cwd=ROOT, env=env))
    if not installed.resolve().is_relative_to(stage.resolve()):
        raise ValueError('installation outside private prefix')
    required(compiler + ['--install', 'fibril.ipkg'], cwd=ROOT, env=env)
    env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join([str(installed.parent), *external])
    fixture = ROOT / 'tools/fixtures/json-admission/Measure.idr'
    source = fixture.read_text().replace('import System\n', 'import System\nimport Data.List\n')
    source = replace_once(source, '("CORE_NODES="', '("GLOBALS=" ++ show (length declarations) ++ " CORE_NODES="')
    (work / 'Measure.idr').write_text(source)
    (work / 'measure.ipkg').write_text('package composed-measure\nsourcedir = "."\ndepends = fibril, yaml\nmain = Measure\nexecutable = measure\n')
    required(compiler + ['--build', 'measure.ipkg'], cwd=work, env=env)
    return work / 'build/exec/measure'


def generated(root, family, size):
    root.mkdir()
    if family in ('inventory', 'chain'):
        # Ordinary modules, at most 32 globals each: preserve the parser's
        # 64-declaration policy while exercising larger legal inventories.
        total = size if family == 'inventory' else size + 1
        modules = (total + 31) // 32
        for module in range(modules):
            lines = [f'module M{module}']
            if family == 'chain' and module:
                lines += [f'import M{module - 1}']
            for index in range(module * 32, min((module + 1) * 32, total)):
                body = '"ok"' if family == 'inventory' or index == 0 else f'if True then g{index - 1} else g{index - 1}'
                lines += ['export', f'g{index} : String', f'g{index} = {body}']
            (root / f'M{module}.fib').write_text('\n'.join(lines) + '\n')
        imports = [f'import M{module}' for module in range(modules)] if family == 'inventory' else [f'import M{modules - 1}']
        target = 'M0.g0' if family == 'inventory' else f'M{modules - 1}.g{size}'
        path = root / 'Main.fib'
        path.write_text('\n'.join(['module Main', *imports, 'main : IO Unit', f'main = putStrLn {target}']) + '\n')
        return path
    if family == 'single-module':
        lines = ['module Main']
        for index in range(size):
            lines += [f'g{index} : String', f'g{index} = "ok"']
        lines += ['main : IO Unit', 'main = putStrLn g0']
    elif family == 'recompute':
        lines = ['module Main', 'g0 : Bool', 'g0 = True']
        for index in range(1, size + 1):
            lines += [f'g{index} : Bool', f'g{index} = if g{index - 1} then g{index - 1} else False']
        lines += ['main : IO Unit', f'main = if g{size} then putStrLn "ok" else putStrLn "wrong"']
    else:
        raise ValueError(family)
    path = root / 'Main.fib'
    path.write_text('\n'.join(lines) + '\n')
    return path


def native(work, code, binary, cc, observed):
    work.mkdir()
    (work / 'program.c').write_bytes(code)
    for path in (ROOT / 'runtime/native').iterdir():
        if path.is_file():
            shutil.copyfile(path, work / path.name)
    if observed:
        instrument(work)
    runtime = 'fibril_binary_runtime.c' if binary else 'fibril_runtime.c'
    required(cc + ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror', '-I', work,
                  work / 'program.c', work / runtime, '-o', work / 'native'])
    return work / 'native'


def extract_profile(row):
    matches = re.findall(r'^COMPOSED (.+)\n', row['stderr'], re.M)
    if row['outcome'] == 'timeout':
        return None
    if len(matches) != 1:
        raise ValueError(('missing/duplicate profile', row))
    row['stderr'] = re.sub(r'^COMPOSED .+\n', '', row['stderr'], flags=re.M)
    profile = json.loads(matches[0])
    if sum(pair[1] for pair in profile['allocations'].values()) != profile['allocated_payload']:
        raise ValueError(('unattributed allocation payload', profile))
    if not (profile['final_arena_payload'] <= profile['peak_arena_payload'] <= profile['allocated_payload']):
        raise ValueError(('invalid payload accounting', profile))
    return profile


def measure_entry(work, measure, label, root, path, binary, inputs, count, timeout, cc):
    print(label, flush=True)
    args = ['--source-dir', root, path]
    row = {'entry': label, 'source_sha256': digest(path), 'binary': binary,
           'module_sources_sha256': {str(p.relative_to(root)): digest(p) for p in sorted(root.rglob('*.fib'))},
           'scope': 'admission-only' if inputs is None else 'checked execution',
           'check': samples([EXE, 'check', *args], count, timeout=timeout), 'runs': []}
    if any(s['outcome'] != 'success' for s in row['check']['samples']):
        return row
    measured = required([measure, root, path])
    match = re.fullmatch(r'GLOBALS=(\d+) CORE_NODES=(\d+) PAYLOAD=(\d+)', measured)
    if not match:
        raise ValueError(measured)
    row['graph'] = dict(zip(('reachable_globals', 'nodes', 'payload_characters'), map(int, match.groups())))
    emission = timed([EXE, 'emit-c-binary' if binary else 'emit-c', *args], timeout=timeout)
    code = bytes.fromhex(emission.pop('stdout_hex'))
    row['emission'] = emission
    row['generated_c_bytes'] = len(code)
    if emission['outcome'] != 'success' or inputs is None:
        return row
    directory = work / label
    directory.mkdir()
    plain = native(directory / 'plain', code, binary, cc, False)
    observed = native(directory / 'observed', code, binary, cc, True)
    for name, data, expected in inputs:
        baseline = samples([plain], count, data, timeout)
        counters = timed([observed], data, timeout)
        profile = extract_profile(counters)
        for sample in baseline['samples']:
            for key in ('outcome', 'returncode', 'stdout_hex', 'stderr'):
                if sample[key] != counters[key]:
                    raise AssertionError(('counter observer changed outcome', label, name, key, sample, counters))
            if sample['outcome'] == 'success' and bytes.fromhex(sample['stdout_hex']) != expected:
                raise AssertionError(('wrong output', label, name, sample))
        run = {'case': name, 'input_hex': data.hex(), 'expected_output_hex': expected.hex(),
               'native': baseline, 'profile': profile, 'counter_observer_matches': True}
        if not binary:
            hosted = samples([EXE, 'run', *args], count, data, timeout)
            for sample in hosted['samples']:
                if sample['outcome'] == 'success' and bytes.fromhex(sample['stdout_hex']) != expected:
                    raise AssertionError(('wrong hosted output', label, name, sample))
            run['hosted_including_check'] = hosted
        row['runs'].append(run)
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'build/benchmarks/composed.json')
    parser.add_argument('--samples', type=int, choices=range(1, 6), default=3)
    parser.add_argument('--timeout', type=int, choices=range(1, 121), default=60)
    parser.add_argument('--smoke', action='store_true')
    args = parser.parse_args()
    cc = shlex.split(os.environ.get('CC', 'cc'))
    compiler = pinned_compiler()
    inputs = sorted({p for folder in ('src', 'stdlib', 'runtime/native', 'tools/fixtures', 'examples/modules')
                     for p in (ROOT / folder).rglob('*') if p.is_file()} |
                    {ROOT / 'tools/probe_composed.py', ROOT / 'pack.toml', ROOT / 'fibril.ipkg',
                     ROOT / 'tools/probe_lsp_workload.py', ROOT / 'tools/probe_lsp_cost_audit.py',
                     ROOT / 'tools/observe_json_state_sharing.py', ROOT / 'tools/test_composed_probe.py',
                     ROOT / 'Makefile'})
    evidence = {'schema': 'fibril-composed-shared-v1', 'representation': 'reachable-shared-graph',
        'complete': False, 'started_utc': datetime.now(timezone.utc).isoformat(),
        'revision': required(['git', 'rev-parse', 'HEAD'], cwd=ROOT),
        'git_status': required(['git', 'status', '--porcelain'], cwd=ROOT),
        'platform': platform.platform(), 'machine': platform.machine(), 'python': sys.version,
        'cc_version': required(cc + ['--version']), 'cc_flags': '-std=c11 -O2 -Wall -Wextra -Werror',
        'idris2_command': compiler, 'idris2_launcher_sha256': digest(shutil.which(compiler[0])),
        'idris2_version': required(compiler + ['--version']),
        'pack_launcher_sha256': digest(shutil.which(shlex.split(os.environ.get('PACK', 'pack'))[0])),
        'compiler_launcher_sha256': digest(EXE),
        'compiler_image_sha256': digest(ROOT / 'build/exec/fibril_app/fibril.so'),
        'inputs_sha256': {str(p.relative_to(ROOT)): digest(p) for p in inputs},
        'samples': args.samples, 'timeout_seconds_per_process': args.timeout,
        'timing': 'fresh process; startup included; no warmup; native C compilation excluded',
        'rss': 'per-command /usr/bin/time maximum RSS; bytes; not arena payload or host allocation totals',
        'scope': 'offline complete-buffer+EOF; admission probes are not protocol pipelines; no budget changes',
        'entries': []}
    with tempfile.TemporaryDirectory(prefix='fibril-composed-') as temporary:
        work = Path(temporary)
        measure = build_measure(work, compiler)
        # Observer preparation is outside measured samples. Record the actual
        # compiler image used at the start of the matrix, then verify at exit.
        evidence['compiler_launcher_sha256'] = digest(EXE)
        evidence['compiler_image_sha256'] = digest(ROOT / 'build/exec/fibril_app/fibril.so')
        def collect(label, root, path, binary=False, cases=None):
            row = measure_entry(work, measure, label, root, path, binary, cases,
                                args.samples, args.timeout, cc)
            evidence['entries'].append(row)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True) + '\n')
        email = ROOT / 'test/fixtures/modules/email-service-full'
        expected = b'sending\ndeferred\nqueued\nfailed\ndelivered\nbounced\nsubmission unknown\ntransition rejected\n'
        collect('email-full', email, email / 'Main.fib', cases=[('demo', b'', expected)])
        for family, sizes in [('inventory', [16, 64, 128, 256, 512]), ('chain', [8, 32, 64, 128, 253, 254, 255, 256]),
                              ('recompute', [4, 8, 10, 12, 14, 15, 16]), ('single-module', [63, 64])]:
            for size in sizes[:1] if args.smoke else sizes:
                root = work / f'source-{family}-{size}'
                path = generated(root, family, size)
                collect(f'{family}-{size}', root, path, cases=[('demo', b'', b'ok\n')])
        if not args.smoke:
            composed = prepare_root(work)
            for name in ('FullIdFour', 'EchoThenTyped', 'JSONThenTyped', 'EchoJSONThenTyped'):
                collect(name, composed, composed / (name + '.fib'), True)
            root = ROOT / 'tools/fixtures/json-iteration'
            cases = []
            for size in (2, 16, 32, 48, 64, 65):
                data = b'"' + b'a' * (size - 2) + b'"'
                expected = oracle(data)[2]
                cases.append((f'string-{size}', data, expected))
            dense = b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']'
            cases.append(('dense-64', dense, oracle(dense)[2]))
            collect('json-read65', root, root / 'Read65.fib', True, cases)
            root = ROOT / 'examples/modules/binary-frame'
            cases = []
            for size in (2, 64, 256, 1024, 4096):
                data = f'Content-Length: {size}\r\n\r\n'.encode() + b'a' * size
                cases.append((f'body-{size}', data, data))
            collect('canonical-frame', root, root / 'Main.fib', True, cases)
    changed = [name for name, checksum in evidence['inputs_sha256'].items()
               if digest(ROOT / name) != checksum]
    if changed or digest(ROOT / 'build/exec/fibril_app/fibril.so') != evidence['compiler_image_sha256']:
        raise RuntimeError(('measurement inputs changed during matrix', changed))
    evidence['complete'] = True
    evidence['finished_utc'] = datetime.now(timezone.utc).isoformat()
    args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True) + '\n')
    print(args.output)


if __name__ == '__main__':
    main()
