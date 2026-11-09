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

DIVIDE = '''divText : (a : Word) -> (b : Word) -> String
divText a b = primWordDivCase String (primWordDiv a b) "divide by zero" (\\(q : Word) => primWordToString q)

remText : (a : Word) -> (b : Word) -> String
remText a b = primWordDivCase String (primWordRem a b) "divide by zero" (\\(q : Word) => primWordToString q)

'''

PROGRAMS = {
    'division': DIVIDE + '''main : IO Unit
main = do
  putStrLn (divText 17w 5w)
  putStrLn (remText 17w 5w)
  putStrLn (divText 17w 0w)
  putStrLn (remText 17w 0w)
  putStrLn (divText 0w 7w)
  putStrLn (divText (primWordSub 0w 1w) 2w)
  putStrLn (remText (primWordSub 0w 1w) 10w)
''',
    'conversion': '''main : IO Unit
main = do
  putStrLn (primWordToString (primWordFromNat 0))
  putStrLn (primWordToString (primWordFromNat 200))
  putStrLn (primWordToString (primWordAdd (primWordFromNat 3) (primWordFromNat 4)))
  putStrLn (primWordToString (primWordMul (primWordFromNat 256) 1000000007w))
''',
    'formatting': '''main : IO Unit
main = do
  putStrLn (primWordToString 0w)
  putStrLn (primWordToString 1000000007w)
  putStrLn (primWordToString (primWordSub 0w 1w))
  putStrLn (appendString "port=" (primWordToString (primWordAdd 8000w 80w)))
''',
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
    'bytes-word-at': '''at : (pos : Word) -> String
at pos = primWordToString (primUTF8Case Bytes Word (primUTF8Encode "abc") 0w
  (\\(1 bytes : Bytes) => primBytesWordAt pos bytes))

main : IO Unit
main = do
  putStrLn (at 0w)
  putStrLn (at 2w)
  putStrLn (at 3w)
  putStrLn (at (primWordSub 0w 1w))
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
        expected = {'division': b'3\n2\ndivide by zero\ndivide by zero\n0\n9223372036854775807\n5\n', 'conversion': b'0\n200\n7\n256000001792\n' , 'formatting': b'0\n1000000007\n18446744073709551615\nport=8080\n', 'false-branches': b'ne\nge\nge\n', 'duplicated-argument': b'wrapped\n',
                    'function-argument-and-nesting': b'hash\n',
                    'bytes-word-at': b'97\n99\n256\n256\n'}
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
