#!/usr/bin/env python3
"""Focused end-to-end checks of the first grouped clause slice."""
from pathlib import Path
import subprocess
import json
import tempfile
import unittest

EXE = Path(__file__).resolve().parents[1] / 'build/exec/fibril'
DATA = '''module Main
data Sum (0 A : Type) (0 B : Type) : Type where
  Left : (1 value : A) -> Sum A B
  Right : (1 value : B) -> Sum A B
'''

class PatternClauses(unittest.TestCase):
    def run_source(self, source):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Main.fib'
            path.write_text(source)
            return subprocess.run([str(EXE), 'eval', '--source-dir', directory, str(path)],
                                  text=True, capture_output=True, timeout=20)

    def test_generic_sum_runs_both_constructors(self):
        for constructor in ('Left', 'Right'):
            result = self.run_source(DATA + f'''get : (1 value : Sum Bool Bool) -> Bool
get Left x = x
get Right x = x
main : Bool
main = get ({constructor} Bool Bool True)
''')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('Normal: True', result.stdout)

    def test_rejections(self):
        cases = [
            'get Left x = x\nget Left y = y',
            'get Left x = x\nget Missing y = y',
            'get Left x = x\nget Right = True',
            'get Left x = get (Left Bool Bool x)\nget Right y = y',
            'get Left x = x\nget y = y',
            'get (Left x) = x\nget Right y = y',
            'get Left x = x\nget Right y = x',
            'get Left x = True\nget Right y = y',
            'get Left x = if x then x else x\nget Right y = y',
        ]
        for clauses in cases:
            with self.subTest(clauses=clauses):
                result = self.run_source(DATA + 'get : (1 value : Sum Bool Bool) -> Bool\n' + clauses + '\nmain : Bool\nmain = True\n')
                self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_clause_headers_navigation_and_rename(self):
        source = "f : Bool -> Bool\nf A = True\nf B = False\nf C = True\nmain : Bool\nmain = f True\n"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            path.write_text(source)
            for line in (1, 2, 3, 4, 6):
                column = 8 if line == 6 else 1
                def call(*args):
                    return subprocess.run([str(EXE), *args, str(path)], text=True, capture_output=True)
                refs = call('references', str(line), str(column))
                self.assertEqual(refs.returncode, 0, refs.stderr)
                spans = json.loads(refs.stdout)['references']
                self.assertEqual([x['start']['line'] for x in spans], [1, 2, 3, 4, 6])
                definition = call('definition', str(line), str(column))
                self.assertEqual(definition.returncode, 0, definition.stderr)
                self.assertEqual(json.loads(definition.stdout)['definition']['start']['line'], 2)
                rename = call('rename-preview', str(line), str(column), 'renamed')
                self.assertEqual(rename.returncode, 0, rename.stderr)
                self.assertEqual([x['range']['start']['line'] for x in json.loads(rename.stdout)['edits']], [1, 2, 3, 4, 6])

    def test_clause_payload_binders_are_distinct(self):
        source = "f : Bool -> Bool\nf A x = x\nf B x = x\nmain : Bool\nmain = True\n"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            path.write_text(source)
            for line in (2, 3):
                for column in (5, 9):
                    result = subprocess.run([str(EXE), 'rename-preview', str(line), str(column),
                                             'item', str(path)], text=True, capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    edits = json.loads(result.stdout)['edits']
                    self.assertEqual([(x['range']['start']['line'], x['range']['start']['column'])
                                      for x in edits], [(line, 5), (line, 9)])

    def test_qualified_other_function_is_not_recursion(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Other.fib').write_text('module Other\nexport\nf : Bool\nf = True\n')
            path = root / 'Main.fib'
            path.write_text("module Main\nimport Other\ndata Choice : Type where\n  One : Choice\n  Two : Choice\nf : Choice -> Bool\nf One = Other.f\nf Two = False\nmain : Bool\nmain = f One\n")
            result = subprocess.run([str(EXE), 'eval', '--source-dir', directory, str(path)], text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('Normal: True', result.stdout)
            for line in (6, 7, 8, 10):
                column = 8 if line == 10 else 1
                definition = subprocess.run([str(EXE), 'definition', '--source-dir', directory,
                                             '--entry', str(path), str(line), str(column), str(path)],
                                            text=True, capture_output=True)
                self.assertEqual(definition.returncode, 0, definition.stderr)
                self.assertEqual(json.loads(definition.stdout)['definition']['range']['start']['line'], 7)

    def test_missing_constructor_rejected(self):
        # Three constructors permit a grouped but non-exhaustive block.
        source = '''module Main
data Choice : Type where
  One : Choice
  Two : Choice
  Three : Choice
f : Choice -> Bool
f One = True
f Two = False
main : Bool
main = True
'''
        result = self.run_source(source)
        self.assertNotEqual(result.returncode, 0, result.stdout)

if __name__ == '__main__':
    unittest.main()
