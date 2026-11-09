#!/usr/bin/env python3
"""Standard-library package tests.

The hosted reference evaluator caps `fibril test` at 4096 fuel, enough for only a handful
of checks, so the small hosted suite is a smoke test. The full conformance program is
compiled to C and run natively, where every check prints one `label: ok` line.
Set FIBRIL_STD_SANITIZE=1 to add ASan/UBSan.
"""
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

RUNTIME = ROOT / 'runtime/native'
STD = ROOT / 'stdlib/std'
CC = shlex.split(os.environ.get('CC', 'cc'))
SANITIZE = (['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g']
            if os.environ.get('FIBRIL_STD_SANITIZE') == '1' else [])
CHECKS = 24  # one report line per conformance check; update with Main.fib


def run_conformance(package_root):
    manifest = package_root / 'conformance/fibril.yaml'
    emitted = run_cli('emit-c', '--package', str(manifest), timeout=300)
    assert emitted.returncode == 0, emitted.stdout + emitted.stderr
    with tempfile.TemporaryDirectory() as directory:
        c_file, exe = Path(directory) / 'std.c', Path(directory) / 'std'
        c_file.write_text(emitted.stdout, encoding='utf-8')
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', *SANITIZE,
                                     '-I', str(RUNTIME), str(c_file), str(RUNTIME / 'fibril_runtime.c'),
                                     '-o', str(exe)], capture_output=True, text=True, timeout=300)
        assert build.returncode == 0, build.stdout + build.stderr
        return subprocess.run([str(exe)], capture_output=True, text=True, timeout=300)


class StdTests(unittest.TestCase):
    def test_library_checks(self):
        result = run_cli('check', '--package', str(STD / 'fibril.yaml'), timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Modules: 3', result.stdout)

    def test_hosted_smoke_suite_passes(self):
        result = run_cli('test', '--package', str(STD / 'fibril.yaml'), '--fuel', '4096', timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Tests: passed', result.stdout)

    def test_native_conformance_every_check_passes(self):
        result = run_conformance(STD)
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = result.stdout.splitlines()
        self.assertEqual(len(lines), CHECKS, result.stdout)
        self.assertTrue(all(line.endswith(': ok') for line in lines), result.stdout)

    def test_a_wrong_expectation_is_reported_not_swallowed(self):
        with tempfile.TemporaryDirectory() as directory:
            copy = Path(directory) / 'std'
            shutil.copytree(STD, copy)
            main = copy / 'conformance/src/Main.fib'
            source = main.read_text(encoding='utf-8')
            self.assertIn('primWordEq (sum three) 6w', source)
            main.write_text(source.replace('primWordEq (sum three) 6w', 'primWordEq (sum three) 7w', 1), encoding='utf-8')
            result = run_conformance(copy)
        self.assertEqual(result.returncode, 0, result.stderr)
        failed = [line for line in result.stdout.splitlines() if line.endswith(': FAILED')]
        self.assertEqual(failed, ['foldLeft sums: FAILED'], result.stdout)


if __name__ == '__main__':
    unittest.main()
