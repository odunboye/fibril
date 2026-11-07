#!/usr/bin/env python3
"""Observe blocked source prototypes, not a success/failure regression test.

Requires `make -j8 build` and this worktree's build/test-prefix installation
(produced by tools/test_units.py). Never installs packages or changes budgets.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tools/fixtures/json-admission'


def observe(command, *, data=None, env=None, cwd=ROOT):
    process = subprocess.Popen(command, stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               cwd=cwd, env=env, start_new_session=True)
    try:
        out, err = process.communicate(data, timeout=120)
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            stream.close()
    print(json.dumps({'command': [str(arg) for arg in command],
                      'status': process.returncode,
                      'stdout_hex': out.hex(),
                      'stderr': err.decode(errors='replace')}), flush=True)
    return process.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--variant', action='append',
                        choices=['full', 'scalar', 'factored', 'shared'],
                        help='observe only this variant (repeatable)')
    variants = parser.parse_args().variant or ['full', 'scalar', 'factored', 'shared']
    pack = shlex.split(os.environ.get('PACK', 'pack'))
    # Pack's idris2 shim resets IDRIS2_PACKAGE_PATH and depends on cwd config.
    # Resolve its real compiler here so the private library environment survives.
    idris = (shlex.split(os.environ['IDRIS2']) if 'IDRIS2' in os.environ else
             [subprocess.check_output(pack + ['--log-level=silence', 'app-path', 'idris2'],
                                      cwd=ROOT, text=True).splitlines()[-1]])
    prefix = ROOT / 'build/test-prefix'
    if prefix.is_symlink() or not prefix.resolve().is_relative_to(ROOT):
        raise SystemExit('Refusing a test prefix outside this worktree')
    packages = list(prefix.glob('idris2-*/fibril-*'))
    if len(packages) != 1:
        raise SystemExit('First stage the worktree library with tools/test_units.py')
    env = os.environ.copy()
    paths = subprocess.check_output(pack + ['--log-level=silence', 'package-path'],
                                    cwd=ROOT, text=True).splitlines()[-1].split(os.pathsep)
    external = [path for path in paths if Path(path).parent.parent.name != 'fibril']
    env['IDRIS2_PREFIX'] = str(prefix)
    env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join([str(packages[0].parent), *external])
    for key, flag in [('IDRIS2_LIBS', 'libs-path'), ('IDRIS2_DATA', 'data-path')]:
        env[key] = subprocess.check_output(pack + ['--log-level=silence', flag],
                                          cwd=ROOT, text=True).splitlines()[-1]
    exe = os.environ.get('FIBRIL', str(ROOT / 'build/exec/fibril'))
    with tempfile.TemporaryDirectory(prefix='fibril-json-observe-') as tmp:
        work = Path(tmp)
        (work / 'Measure.idr').write_text((FIXTURES / 'Measure.idr').read_text())
        package = work / 'measure.ipkg'
        package.write_text('package json-admission-measure\ndepends = fibril\n'
                           'sourcedir = "."\nmain = Measure\nexecutable = measure\n')
        built = observe(idris + ['--build', str(package)], env=env, cwd=work)
        if built:
            raise SystemExit('Could not build observer against worktree-local library')
        metric = str(work / 'build/exec/measure')
        for variant in variants:
            source = FIXTURES / variant
            entries = ['Main.fib'] if variant == 'scalar' else ['Parse.fib', 'Main.fib']
            if variant == 'shared':
                entries.append('Read65.fib')
            for name in entries:
                entry = source / name
                observe([metric, str(source), str(entry)])
                observe([exe, 'check', '--source-dir', str(source), str(entry)])
                if name != 'Parse.fib':
                    observe([exe, 'run-binary', '--source-dir', str(source), str(entry)],
                            data=b'1')
                    observe([exe, 'emit-c-binary', '--source-dir', str(source), str(entry)])


if __name__ == '__main__':
    main()
