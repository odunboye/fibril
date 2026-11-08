#!/usr/bin/env python3
"""Offline reservation/emitted-size ledger in a private checker copy.

Trace allocation/printing is observer overhead, not a time/heap measurement.
No production estimator, limit, checker decision or budget update is rewritten.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import shlex
import tempfile

from probe_composed import ROOT, EXE, digest, required, pinned_compiler, replace_once
from probe_lsp_cost_audit import prepare_root
from probe_lsp_workload import run_process


def instrument(source):
    source = replace_once(source, 'module Fibril.Driver.ModuleCheck\n',
                          'module ObservedModuleCheck\n\nimport Debug.Trace\n')
    expression = ('cost remaining globals [] decl.expected + cost remaining globals [] decl.value + '
                  'recursiveEquationReserveGlobals shared decl.name decl.value')
    full = expression.replace('cost remaining', 'cost 200000')
    source = replace_once(source, '  let estimate = ' + expression,
        '  let estimate = trace ("RESERVE " ++ moduleText name ++ "." ++ decl.name ++ " " ++ show remaining ++ " " ++\n'
        '        show (' + full + ')) (' + expression + ')')
    source = replace_once(source, '  let key = length (globalDeclarations (erasedGlobals shared))',
        '  let key = trace ("BUILT " ++ moduleText name ++ "." ++ decl.name ++ " " ++\n'
        '        show (nodes ty + nodes value)) (length (globalDeclarations (erasedGlobals shared)))')
    source = replace_once(source, '  let reservation : Nat = 128',
        '  let reservation : Nat = trace ("RESERVE " ++ moduleText moduleName ++ "." ++ group.first.name ++ "+" ++ group.second.name ++\n'
        '        " " ++ show remaining ++ " 128") 128')
    source = replace_once(source, '  let firstKey = length (globalDeclarations (erasedGlobals shared))',
        '  let firstKey = trace ("BUILT " ++ moduleText moduleName ++ "." ++ group.first.name ++ "+" ++ group.second.name ++ " " ++\n'
        '        show (nodes ty0 + nodes ty1 + nodes value0 + nodes value1)) (length (globalDeclarations (erasedGlobals shared)))')
    source = replace_once(source,
        '      compiled <- compileDeclarationsGlobals shared snapshot header.components globals declarations remaining',
        '      compiled <- map (\\completed => trace ("FINISH " ++ moduleText header.components ++ " " ++ show completed.remaining) completed)\n'
        '        (compileDeclarationsGlobals shared snapshot header.components globals declarations remaining)')
    return source


HARNESS = '''module {module}
import System
import Data.List
import {checker}
import Fibril.Driver.ModuleGraph
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Runtime
import Fibril.Core.Erased
import Fibril.Core.SharedProgram

covering
main : IO ()
main = do
  [_, root, entry] <- getArgs | _ => exitFailure
  result <- checkProject root entry
  case result of
    Left err => do
      putStrLn "RESULT rejected"
      putStrLn (renderGraphError err)
      exitFailure
    Right project => case reachableGlobals project.globals project.term of
      Left message => do putStrLn message; exitFailure
      Right declarations => putStrLn ("RESULT accepted " ++
        show (globalSyntaxNodes (erasedGlobals project.globals)) ++ " " ++
        show (sharedProgramNodes project.term declarations))
'''


def build(work):
    compiler = pinned_compiler()
    pack = shlex.split(os.environ.get('PACK', 'pack'))
    env = os.environ.copy()
    for key, flag in [('IDRIS2_PACKAGE_PATH', 'package-path'), ('IDRIS2_LIBS', 'libs-path'), ('IDRIS2_DATA', 'data-path')]:
        paths = [line for line in required(pack + ['--log-level=silence', flag], cwd=ROOT).splitlines() if line.startswith('/')]
        if len(paths) != 1:
            raise ValueError(('ambiguous curated paths', paths))
        env[key] = paths[0]
    external = [p for p in env['IDRIS2_PACKAGE_PATH'].split(os.pathsep) if Path(p).parent.parent.name != 'fibril']
    prefix = ROOT / 'build/construction-prefix'
    if prefix.is_symlink() or not prefix.resolve().is_relative_to(ROOT):
        raise ValueError('unsafe private prefix')
    env['IDRIS2_PREFIX'] = str(prefix)
    env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join(external)
    installed = Path(required(compiler + ['--dump-installdir', 'fibril.ipkg'], cwd=ROOT, env=env))
    if not installed.resolve().is_relative_to(prefix.resolve()):
        raise ValueError('installation outside private prefix')
    required(compiler + ['--install', 'fibril.ipkg'], cwd=ROOT, env=env)
    env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join([str(installed.parent), *external])
    original = (ROOT / 'src/Fibril/Driver/ModuleCheck.idr').read_text()
    (work / 'ObservedModuleCheck.idr').write_text(instrument(original))
    for module, checker in [('PlainAudit', 'Fibril.Driver.ModuleCheck'), ('Audit', 'ObservedModuleCheck')]:
        (work / (module + '.idr')).write_text(HARNESS.format(module=module, checker=checker))
        (work / (module + '.ipkg')).write_text(f'package construction-{module.lower()}\nsourcedir = "."\ndepends = fibril, yaml\nmain = {module}\nexecutable = {module}\n')
        required(compiler + ['--build', module + '.ipkg'], cwd=work, env=env)
    return work / 'build/exec/PlainAudit', work / 'build/exec/Audit'


def parse(text):
    ledger, ordinary = [], []
    for line in text.splitlines():
        if line.startswith('RESERVE '):
            _, name, remaining, estimate = line.split()
            ledger.append({'event': 'reserve', 'name': name, 'remaining': int(remaining),
                           'full_estimate': int(estimate)})
        elif line.startswith('BUILT '):
            _, name, nodes = line.split()
            ledger.append({'event': 'built', 'name': name, 'nodes': int(nodes)})
        elif line.startswith('FINISH '):
            _, name, remaining = line.split()
            ledger.append({'event': 'finish', 'name': name, 'remaining': int(remaining)})
        else:
            ordinary.append(line)
    return ledger, '\n'.join(ordinary)


def validate_ledger(ledger, result, committed):
    """Check reservation bounds and cross-declaration conservation, not CPU work."""
    remaining, retained, estimates, peak = 200000, 0, 0, 0
    active = None
    for row in ledger:
        if row['event'] == 'reserve':
            if active is not None or row['remaining'] != remaining or row['full_estimate'] < 0:
                raise ValueError(('reservation ledger discontinuity', row))
            active = row
        elif row['event'] == 'built':
            if (active is None or row['name'] != active['name'] or
                    not 0 <= row['nodes'] <= active['full_estimate'] <= remaining):
                raise ValueError(('emitted syntax exceeds reserved allowance', row, active))
            peak = max(peak, retained + active['full_estimate'])
            retained += row['nodes']
            estimates += active['full_estimate']
            remaining -= row['nodes'] if committed else active['full_estimate']
            active = None
        elif row['event'] == 'finish':
            if active is not None or row['remaining'] != remaining:
                raise ValueError(('module completion does not conserve remaining allowance', row))
        else:
            raise ValueError(('unknown ledger event', row))
    if result.startswith('RESULT accepted '):
        _, _, stored, reachable = result.split()
        if active is not None or int(stored) != retained or retained + 1 > 200000 or remaining < 1:
            raise ValueError('accepted project footprint does not reconcile with ledger')
    return {'emitted_nodes': retained, 'completed_reservations': estimates,
            'remaining': remaining, 'maximum_retained_plus_active_reservation': peak,
            'pending': active}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    paths = [p for folder in ('src', 'stdlib', 'tools/fixtures/lsp-cost-audit',
                              'tools/fixtures/json-iteration', 'tools/fixtures/lsp-lifecycle',
                              'examples/modules/binary-frame') for p in (ROOT / folder).rglob('*') if p.is_file()]
    paths += [Path(__file__), ROOT / 'tools/probe_composed.py', ROOT / 'tools/probe_lsp_cost_audit.py',
              ROOT / 'tools/probe_lsp_workload.py', ROOT / 'fibril.ipkg', ROOT / 'pack.toml']
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in sorted(set(paths))}
    committed = 'minus remaining constructed' in (ROOT / 'src/Fibril/Driver/ModuleCheck.idr').read_text()
    image = digest(ROOT / 'build/exec/fibril_app/fibril.so')
    report = {'schema': 'fibril-construction-ledger-v1', 'complete': False, 'revision': required(['git', 'rev-parse', 'HEAD'], cwd=ROOT),
              'git_status': required(['git', 'status', '--porcelain'], cwd=ROOT),
              'platform': platform.platform(), 'inputs_sha256': hashes, 'compiler_image_sha256': image,
              'scope': 'offline source reservation/emitted syntax; no CPU/heap or wire execution claims',
              'accounting': 'committed-output' if committed else 'cumulative-reservations', 'entries': []}
    with tempfile.TemporaryDirectory(prefix='fibril-construction-') as temporary:
        work = Path(temporary)
        plain, observed = build(work)
        # Preparing the private package may rebuild the executable. Capture the
        # actual image used by the matrix after preparation, then verify at exit.
        image = digest(ROOT / 'build/exec/fibril_app/fibril.so')
        report['compiler_image_sha256'] = image
        root = prepare_root(work)
        for name in ('FullIdFour', 'EchoThenTyped', 'JSONThenTyped', 'EchoJSONThenTyped'):
            command = [root, root / (name + '.fib')]
            baseline = run_process([plain, *command], timeout=120)
            actual = run_process([observed, *command], timeout=120)
            ledger, text = parse(actual.stdout.decode())
            assert actual.returncode == baseline.returncode, name
            assert actual.stderr == baseline.stderr == b'', name
            assert text == baseline.stdout.decode().strip(), name
            cli = run_process([EXE, 'check', '--source-dir', *command], timeout=120)
            assert cli.returncode == actual.returncode, name
            report['entries'].append({'entry': name, 'returncode': actual.returncode,
                                      'result': text, 'ledger': ledger, 'observer_matches': True,
                                      'summary': validate_ledger(ledger, text, committed)})
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
            print(name, text.splitlines()[0], flush=True)
    assert all(digest(ROOT / name) == checksum for name, checksum in hashes.items())
    assert digest(ROOT / 'build/exec/fibril_app/fibril.so') == image
    report['complete'] = True
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(args.output)


if __name__ == '__main__':
    main()
