#!/usr/bin/env python3
"""Differential Word tests: native C output must equal the reference runner's.

Words reach output only through Bool branches, so each program prints which branch ran.
Set FIBRIL_WORD_SANITIZE=1 to add ASan/UBSan.
"""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli

RUNTIME = ROOT / 'runtime/native'
CC = shlex.split(os.environ.get('CC', 'cc'))
SANITIZE = (['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g']
            if os.environ.get('FIBRIL_WORD_SANITIZE') == '1' else [])

PROGRAMS = {
    'false-branches': '''main : IO Unit
main = do
  putStrLn (if primWordEq 1w 2w then "eq" else "ne")
  putStrLn (if primWordLt 5w 5w then "lt" else "ge")
  putStrLn (if primWordLt 18446744073709551615w 0w then "lt" else "ge")
''',
    'duplicated-argument': '''dbl : (x : Word) -> Word
dbl x = primWordAdd x x

main : IO Unit
main = putStrLn (if primWordEq (dbl 9223372036854775808w) 0w then "wrapped" else "no")
''',
    'function-argument-and-nesting': '''step : (acc : Word) -> (x : Word) -> Word
step acc x = primWordAdd (primWordMul acc 31w) x

main : IO Unit
main = putStrLn (if primWordEq (step (step (step 7w 1w) 2w) 3w) 209563w then "hash" else "mismatch")
''',
}


class WordNativeTests(unittest.TestCase):
    def native(self, path, directory):
        emitted = run_cli('emit-c', str(path), timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        c_file, exe = Path(directory) / 'p.c', Path(directory) / 'p'
        c_file.write_text(emitted.stdout, encoding='utf-8')
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', *SANITIZE,
                                     '-I', str(RUNTIME), str(c_file), str(RUNTIME / 'fibril_runtime.c'),
                                     '-o', str(exe)], capture_output=True, text=True, timeout=120)
        self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
        result = subprocess.run([str(exe)], capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def check(self, path, directory):
        reference = run_cli('run', str(path), text=False, timeout=120)
        self.assertEqual(reference.returncode, 0, reference.stderr)
        self.assertEqual(self.native(path, directory), reference.stdout)
        return reference.stdout

    def test_example_matches_reference_and_every_property_holds(self):
        with tempfile.TemporaryDirectory() as directory:
            out = self.check(ROOT / 'examples/core/word-native.fib', directory)
            self.assertEqual(out.count(b': ok'), 5)
            self.assertNotIn(b'FAILED', out)

    def test_programs_match_reference(self):
        expected = {'false-branches': b'ne\nge\nge\n', 'duplicated-argument': b'wrapped\n',
                    'function-argument-and-nesting': b'hash\n'}
        for name, source in PROGRAMS.items():
            with self.subTest(program=name), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'Main.fib'
                path.write_text(source, encoding='utf-8')
                self.assertEqual(self.check(path, directory), expected[name])

    def test_emitted_code_uses_unsigned_literals_not_source_text(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text('main : IO Unit\nmain = putStrLn (if primWordEq 18446744073709551615w 0w then "a" else "b")\n')
            emitted = run_cli('emit-c', str(path), timeout=120).stdout
            self.assertIn('UINT64_C(18446744073709551615)', emitted)


if __name__ == '__main__':
    unittest.main()
