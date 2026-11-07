#!/usr/bin/env python3
"""Bounded candidate-only source-sharing measurements. No wire pipeline claim."""
import argparse
from collections import Counter
from contextlib import contextmanager
import hashlib
import math
import json
import os
import platform
import sys
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile
import unittest

from lsp_source_sharing import (ROOT, CANDIDATE, BASELINES, source_preservation,
                                bare, closed, expand_introduced, instrument_module_check)
from probe_lsp_cost_audit import digest, syntax_identity, compile_native, execute
from probe_lsp_workload import run_process, checked
from test_binary_iteration import observe
from lsp_cost_instrument import instrument
from observe_json_state_sharing import oracle

EXE = ROOT / 'build/exec/fibril'
BUILD = ROOT / 'build/lsp-source-sharing'
JSON_ROOT = ROOT / 'tools/fixtures/json-iteration'
FRAME_ROOT = ROOT / 'examples/modules/binary-frame'


def captured_process(command, *, cwd=None, env=None, input=None, timeout=120):
    if isinstance(command, (str, bytes)):
        raise TypeError('candidate launches require an argument sequence')
    if input is not None and not isinstance(input, bytes):
        raise TypeError('candidate launches require bytes input')
    if not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('candidate launches require a finite positive timeout')
    args = list(map(str, command))
    if env is not None:
        args = ['env', '-i'] + [f'{k}={v}' for k,v in env.items()] + args
    if cwd is not None:
        args = ['bash', '-c', 'cd -- "$1" || exit; shift; exec "$@"', 'source-sharing-build', str(cwd)] + args
    result = run_process(args, input=input, timeout=timeout)
    return subprocess.CompletedProcess(command, result.returncode, result.stdout, result.stderr)


def process(command, **kwargs):
    result = captured_process(command, **kwargs)
    assert result.returncode == 0, (command, result.stdout, result.stderr)
    return result


class CapturedSubprocessProxy:
    """Only the suites' captured-byte run calls change; live Popen stays original."""
    def __init__(self, original):
        self.original = original

    def __getattr__(self, name):
        return getattr(self.original, name)

    def run(self, command, *, capture_output, timeout, input=None, cwd=None, env=None):
        # Deliberately reject unsupported subprocess.run options rather than
        # silently losing stream, text, shell or check semantics.
        if capture_output is not True:
            raise ValueError('candidate run calls require capture_output=True')
        return captured_process(command, cwd=cwd, env=env, input=input, timeout=timeout)


@contextmanager
def candidate_suite_routing(evidence):
    import test_json_iteration as j
    import test_framing as f
    saved = [(module, name, getattr(module, name)) for module, names in
             ((j, ('FIXTURE', 'checked', 'subprocess')),
              (f, ('SOURCE', 'ENTRY', 'run', 'subprocess'))) for name in names]

    def json_checked(command, **kwargs):
        result = process(command, **kwargs)
        if '--install' in command:
            evidence['compiler_image_after_json_staging_sha256'] = digest(ROOT/'build/exec/fibril_app/fibril.so')
        return result

    def frame_run(command, data=b''):
        result = captured_process(command, cwd=f.ROOT, input=data, timeout=90)
        return result.returncode, result.stdout, result.stderr

    try:
        j.FIXTURE, j.checked = CANDIDATE, json_checked
        j.subprocess = CapturedSubprocessProxy(j.subprocess)
        f.SOURCE, f.ENTRY, f.run = CANDIDATE, CANDIDATE / 'Main.fib', frame_run
        f.subprocess = CapturedSubprocessProxy(f.subprocess)
        yield j, f
    finally:
        for module, name, original in reversed(saved):
            setattr(module, name, original)


def build_audits():
    BUILD.mkdir(parents=True, exist_ok=True)
    compiler = shlex.split(os.environ['IDRIS2'])
    env = os.environ.copy()
    env['IDRIS2_PREFIX'] = str(ROOT / 'build/test-prefix')
    process(compiler + ['--install', 'fibril.ipkg'], cwd=ROOT, env=env)
    installed = Path(process(compiler + ['--dump-installdir', 'fibril.ipkg'], cwd=ROOT, env=env).stdout.decode().strip())
    assert installed.resolve().is_relative_to((ROOT / 'build/test-prefix').resolve())
    env['IDRIS2_PACKAGE_PATH'] = str(installed.parent) + os.pathsep + env['IDRIS2_PACKAGE_PATH']
    original = (ROOT / 'tools/fixtures/lsp-cost-audit/Audit.idr').read_text()
    (BUILD / 'Audit.idr').write_text(original)
    counted = instrument_module_check((ROOT / 'src/Fibril/Driver/ModuleCheck.idr').read_text())
    (BUILD / 'CountedModuleCheck.idr').write_text(counted)
    needle = '"{\\"core_nodes\\":"'
    assert original.count(needle) == 1
    (BUILD / 'CountedAudit.idr').write_text(original.replace('module Audit', 'module CountedAudit', 1)
        .replace('import Fibril.Driver.ModuleCheck', 'import CountedModuleCheck', 1)
        .replace(needle, '"{\\"construction_debit\\":" ++ show project.constructionDebit ++ ",\\"declaration_debit\\":" ++ show project.declarationDebit ++ ",\\"main_reservation\\":" ++ show project.mainReservation ++ ",\\"core_nodes\\":"'))
    for name, main in [('audit', 'Audit'), ('counted', 'CountedAudit')]:
        (BUILD / (name + '.ipkg')).write_text(f'package source-sharing-{name}\nsourcedir = "."\ndepends = fibril, yaml\nmain = {main}\nexecutable = {name}\n')
        process(compiler + ['--build', name + '.ipkg'], cwd=BUILD, env=env)
    return {name: digest(BUILD / name) for name in ('CountedModuleCheck.idr', 'CountedAudit.idr', 'Audit.idr')}


def inventory(root, filename):
    command = [BUILD / 'build/exec/counted', root, root / filename]
    result = run_process(command, timeout=120)
    ordinary = run_process([BUILD / 'build/exec/audit', root, root / filename], timeout=120)
    if result.returncode:
        assert result.returncode == ordinary.returncode == 1
        assert b'Expanded core construction budget exhausted (200000)' in result.stderr
        assert b'Expanded core construction budget exhausted (200000)' in ordinary.stderr
        return dict(outcome='construction-blocker', diagnostic=result.stderr.decode().replace(str(root), '<source-root>'),
                    core_nodes=None, payload=None, construction_debit=None)
    assert ordinary.returncode == 0 and not ordinary.stderr and not result.stderr
    counted, baseline = json.loads(result.stdout), json.loads(ordinary.stdout)
    debit = counted.pop('construction_debit')
    declarations, main = counted.pop('declaration_debit'), counted.pop('main_reservation')
    assert debit == declarations + main <= 200000
    assert counted == baseline, 'counter-only clone must exactly agree with ordinary checker'
    return dict(outcome='checked', document=baseline, core_nodes=baseline['core_nodes'],
                payload=baseline['payload_estimate'], construction_debit=debit,
                declaration_debit=declarations, main_reservation=main)


def syntax(evidence, work):
    helpers = {}
    for name, file in [('Frame', 'EqualString.fib'), ('JSON', 'OrBool.fib')]:
        document = json.loads(checked([BUILD / 'build/exec/audit', ROOT / 'tools/fixtures/lsp-cost-audit',
                                      ROOT / 'tools/fixtures/lsp-cost-audit' / file]))
        rhs = document['tree']['children'][1]
        assert closed(rhs)
        helpers[name] = rhs
        size, sha = syntax_identity(rhs)
        evidence['helpers'][name] = dict(closed=True, nodes=size, syntax_sha256=sha,
            argument_quantities='linear, linear', introduced_value_quantity='unrestricted')
    baseline_root = work / 'baseline-source'
    shutil.copytree(CANDIDATE, baseline_root)
    for name, path in BASELINES.items():
        shutil.copyfile(path, baseline_root / f'Protocol/{name}.fib')
    for filename, root, helper in [('Main.fib', FRAME_ROOT, 'Frame'), ('Two.fib', FRAME_ROOT, 'Frame'),
            ('Parse.fib', JSON_ROOT, 'JSON'), ('ParseBinary.fib', JSON_ROOT, 'JSON'),
            ('PureRead65.fib', JSON_ROOT, 'JSON'), ('Read65.fib', JSON_ROOT, 'JSON'),
            ('EchoThenTyped.fib', baseline_root, 'Frame'), ('JSONThenTyped.fib', baseline_root, 'JSON')]:
        old, new = inventory(root, filename), inventory(CANDIDATE, filename)
        row = dict(entry=filename, baseline={k:v for k,v in old.items() if k != 'document'},
                   candidate={k:v for k,v in new.items() if k != 'document'})
        if old['outcome'] == new['outcome'] == 'checked':
            expanded, count = expand_introduced(new['document']['tree'], helpers[helper])
            assert bare(expanded) == bare(old['document']['tree']), filename
            row.update(checked_alias_expansion_exact=True, introduced_binders=count)
        for label, source in [('baseline', root), ('candidate', CANDIDATE)]:
            # Pure function entries are not binary programs; inventory is their check.
            if filename in ('Parse.fib', 'ParseBinary.fib'):
                continue
            result = run_process([EXE, 'emit-c-binary', '--source-dir', source, source / filename], timeout=120)
            if row[label]['outcome'] == 'construction-blocker':
                assert result.returncode == 1 and b'construction budget exhausted' in result.stderr
                outcome = 'construction-blocker; no checked closed size or execution'
            elif row[label]['core_nodes'] > 8192:
                assert result.returncode == 1 and b'Native core admission exceeds 8192 nodes' in result.stderr
                outcome = 'node-admission-blocker; not execution'
            else:
                assert result.returncode == 0 and not result.stderr
                outcome = 'emitted; admission only, not execution'
            row[label]['native_admission'] = outcome
        evidence['syntax'].append(row)


def profiles(evidence, work):
    cases = {'64-token-array': b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']',
             'ASCII-string': b'"' + b'a' * 62 + b'"',
             'UTF8-string': b'"' + 'ÿ'.encode() * 31 + b'"', 'whitespace-value': b' ' * 63 + b'1'}
    for label, root, filename in [('JSON-baseline', JSON_ROOT, 'Read65.fib'), ('JSON-candidate', CANDIDATE, 'Read65.fib'),
                                 ('Frame-baseline', FRAME_ROOT, 'Main.fib'), ('Frame-candidate', CANDIDATE, 'Main.fib')]:
        programs = []
        emitted = checked([EXE, 'emit-c-binary', '--source-dir', root, root / filename])
        for kind in ('observer', 'attributed'):
            directory = work / (label + '-' + kind); directory.mkdir()
            (directory / 'program.c').write_bytes(emitted)
            observe(directory)
            shutil.copyfile(ROOT / 'tools/fixtures/lsp-workload-observer.c', directory / 'observer.c')
            if kind == 'attributed':
                instrument(directory)
            compile_native(directory)
            programs.append(directory)
        inputs = cases if label.startswith('JSON') else {'opaque-4KiB-frame': b'Content-Length: 4096\r\n\r\n' + bytes(range(256)) * 16}
        for case, data in inputs.items():
            expected = oracle(data)[2] if label.startswith('JSON') else data
            plain, metrics, _ = execute([programs[0] / 'native'], data)
            actual, metrics2, counters = execute([programs[1] / 'native'], data)
            assert actual == plain == expected and metrics == metrics2
            assert metrics['consumed_bytes'] == len(data) and metrics['accepted_bytes'] == len(expected)
            assert metrics['callbacks'] == (65 if label.startswith('JSON') else 0)
            assert counters['steps']['unmapped_evaluation'] == 0
            assert sum(counters['steps'].values()) == metrics['steps']
            assert sum(v[1] for v in counters['allocations'].values()) == metrics['arena_payload']
            assert sum(counters['values'].values()) == counters['allocations']['new_value'][0]
            evidence['native'].append(dict(entry=label, case=case, input_bytes=len(data),
                output_sha256=hashlib.sha256(actual).hexdigest(), metrics=metrics, attribution=counters,
                observer_equal=True, instrumented_sha256={p.name:digest(p) for p in programs[1].glob('*') if p.suffix in ('.c', '.h')}))


def suites(evidence):
    with candidate_suite_routing(evidence) as (j, f):
        run_candidate_suites(evidence, j, f)


def run_candidate_suites(evidence, j, f):
    # setUpClass uses temporary per-program roots, populated only from candidate.
    class CandidateJSON(j.JSONIteration):
        @classmethod
        def tearDownClass(cls):
            evidence['json_rows'] = cls.rows
            cls.temporary.cleanup()
    names = ['test_all_prior_cases_and_extended_boundaries', 'test_real_checked_binary_stdio_named_subset',
             'test_api_and_clients_fit_unchanged_admission', 'test_no_parser_transport_and_existing_mode_gates']
    result = unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(CandidateJSON(n) for n in names))
    assert result.wasSuccessful(), 'candidate JSON matrix/gates failed'
    matrix_rows = [r for r in evidence['json_rows'] if 'category' in r]
    totals = {backend:dict(Counter(r['category'] for r in matrix_rows if r['backend'] == backend)) for backend in ('hosted', 'native')}
    assert totals == {backend: {'valid_transfer': 76, 'invalid_json': 43, 'reader_eof': 1} for backend in ('hosted', 'native')}, totals
    evidence['json_matrix_totals'] = totals
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(f.Framing))
    assert result.wasSuccessful() and result.testsRun == 14
    evidence['framing'] = dict(regressions=result.testsRun, failures=0, explicit_candidate_root=True,
                              live_cases='owned processes: oversize early refusal, two-frame flush, fragmented open input')


def source_controls(evidence, work):
    source_preservation('Frame'); source_preservation('JSON')
    for name in BASELINES:
        text = (CANDIDATE / f'Protocol/{name}.fib').read_text()
        try:
            source_preservation(name, text.replace('then', 'else', 1))
        except AssertionError:
            pass
        else:
            raise AssertionError('substantive change passed preservation')
    root = work / 'negative-source'; shutil.copytree(CANDIDATE, root)
    path = root / 'Protocol/JSON.fib'; text = path.read_text()
    for case, altered in [('malformed', text + '\nthis is not a declaration\n'),
                           ('missing-helper', text.replace('= orBool in', '= missingOrBool in', 1))]:
        path.write_text(altered)
        result = run_process([EXE, 'check', '--source-dir', root, root / 'Read65.fib'], timeout=120)
        assert result.returncode == 1 and result.stderr and not result.stdout
        evidence['source_controls'].append(dict(case=case, returncode=result.returncode, stderr=result.stderr.decode().replace(str(root), '<negative-source>')))
    evidence['source_controls'].append(dict(case='non-alias-body-change', rejected=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    evidence = dict(scope='two lexical aliases; source preservation, NOT full grammar formal proof or wire composition',
        base_commit='5ca14f3', cc=os.environ.get('CC','cc'), syntax=[], helpers={}, native=[], source_controls=[],
        construction_semantics='Existing named-module declaration estimate debits plus final main.size reservation (200000 - compiled.remaining + main.size); not allocations or AST size. Saturated refused declaration estimates reported with remaining budget; no unsaturated invented totals.',
        compiler_launcher_sha256=digest(EXE), compiler_image_before_staging_sha256=digest(ROOT/'build/exec/fibril_app/fibril.so'),
        execution_input_contract='complete buffer + EOF except explicitly live owned framing tests',
        platform=platform.platform(), python=sys.version,
        idris2=os.environ['IDRIS2'], idris2_launcher_sha256=digest(os.environ['IDRIS2']),
        idris2_version=checked([os.environ['IDRIS2'], '--version']).decode().strip(),
        cc_version=checked(shlex.split(os.environ.get('CC','cc')) + ['--version']).decode().strip())
    evidence['private_checker_sha256'] = build_audits()
    evidence['compiler_image_before_probes_sha256'] = digest(ROOT/'build/exec/fibril_app/fibril.so')
    inputs = [p for folder in ('src','stdlib','runtime/native','tools/fixtures/lsp-source-sharing',
              'tools/fixtures/lsp-cost-audit','tools/fixtures/json-iteration','examples/modules/binary-frame') for p in (ROOT/folder).rglob('*') if p.is_file()]
    evidence['private_executable_sha256'] = {str(p.relative_to(BUILD)):digest(p) for p in
        (BUILD/'build/exec').rglob('*') if p.is_file() and p.suffix in ('', '.so')}
    inputs += [ROOT/name for name in ('fibril.ipkg', 'Makefile', 'tools/probe_lsp_source_sharing.py',
        'tools/lsp_source_sharing.py', 'tools/test_lsp_source_sharing.py', 'tools/test_json_iteration.py', 'tools/test_framing.py',
        'tools/test_binary_iteration.py', 'tools/lsp_cost_instrument.py', 'tools/probe_lsp_cost_audit.py',
        'tools/probe_lsp_workload.py', 'tools/observe_json_state_sharing.py',
        'tools/fixtures/lsp-workload-observer.c')]
    evidence['inputs_sha256'] = {str(p.relative_to(ROOT)):digest(p) for p in sorted(set(inputs))}
    with tempfile.TemporaryDirectory(prefix='fibril-source-sharing-') as temporary:
        work = Path(temporary)
        source_controls(evidence, work)
        syntax(evidence, work)
        profiles(evidence, work)
        suites(evidence)
    evidence['compiler_image_after_probes_sha256'] = digest(ROOT/'build/exec/fibril_app/fibril.so')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2, sort_keys=True)+'\n')
    print('Candidate observations complete:', args.output)

if __name__ == '__main__':
    main()
