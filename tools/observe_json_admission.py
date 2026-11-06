#!/usr/bin/env python3
"""Observe blocked source prototypes, not a success/failure regression test.

Requires `make -j8 build` and this worktree's build/test-prefix installation
(produced by tools/test_units.py). Never installs packages or changes budgets.
"""
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
    pack = shlex.split(os.environ.get('PACK', 'pack'))
    idris = shlex.split(os.environ.get('IDRIS2', 'idris2'))
    prefix = ROOT / 'build/test-prefix'
    if prefix.is_symlink() or not prefix.resolve().is_relative_to(ROOT):
        raise SystemExit('Refusing a test prefix outside this worktree')
    packages = list(prefix.glob('idris2-*/fibril-*'))
    if len(packages) != 1:
        raise SystemExit('First stage the worktree library with tools/test_units.py')
    env = os.environ.copy()
    paths = subprocess.check_output(pack + ['--log-level=silence', 'package-path'],
                                    cwd=ROOT, text=True).strip().split(os.pathsep)
    external = [path for path in paths if Path(path).parent.parent.name != 'fibril']
    env['IDRIS2_PREFIX'] = str(prefix)
    env['IDRIS2_PACKAGE_PATH'] = os.pathsep.join([str(packages[0].parent), *external])
    for key, flag in [('IDRIS2_LIBS', 'libs-path'), ('IDRIS2_DATA', 'data-path')]:
        env[key] = subprocess.check_output(pack + ['--log-level=silence', flag],
                                          cwd=ROOT, text=True).strip()
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
        for variant, name in [('full', 'Parse.fib'), ('full', 'Main.fib'),
                              ('scalar', 'Main.fib')]:
            source = FIXTURES / variant
            entry = source / name
            observe([metric, str(source), str(entry)])
            observe([exe, 'check', '--source-dir', str(source), str(entry)])
            if name == 'Main.fib':
                observe([exe, 'run-binary', '--source-dir', str(source), str(entry)],
                        data=b'1')
                observe([exe, 'emit-c-binary', '--source-dir', str(source), str(entry)])


if __name__ == '__main__':
    main()
