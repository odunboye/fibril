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

    def test_nat_clauses_and_direct_case(self):
        definitions = [
            'f Zero = Zero\nf Succ n = Succ n',
            'f n = case n of\n  Zero => Zero\n  Succ k => Succ k',
        ]
        for definition in definitions:
            for value in ('Zero', 'Succ Zero'):
                with self.subTest(definition=definition, value=value):
                    result = self.run_source('module Main\nf : Nat -> Nat\n' + definition +
                                             f'\nmain : Nat\nmain = f ({value})\n')
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn('Normal: ' + ('Zero' if value == 'Zero' else '(Succ Zero)'), result.stdout)

    def test_linear_nat_named_equation_direct_case_and_recursion(self):
        definitions = [
            'f n = case n of\n  Zero => Zero\n  Succ k => Succ k',
            'f n = case n of\n  Succ k => Succ k\n  Zero => Zero',
            'f n = case n of\n  Zero => Zero\n  Succ k => Succ (f k)',
        ]
        for definition in definitions:
            for value in ('Zero', 'Succ Zero'):
                with self.subTest(definition=definition, value=value):
                    result = self.run_source('module Main\nf : (1 n : Nat) -> Nat\n' + definition +
                                             f'\nmain : Nat\nmain = f ({value})\n')
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn('Normal: ' + ('Zero' if value == 'Zero' else '(Succ Zero)'), result.stdout)

    def test_linear_nat_named_equation_rejects_invalid_self_recursion(self):
        definitions = [
            'f n = case n of\n  Zero => f Zero\n  Succ k => Succ k',
            'f n = case n of\n  Zero => Zero\n  Succ k => f n',
            'f n = case n of\n  Zero => Zero\n  Succ k => Succ (f (Succ k))',
            'f n = case n of\n  Zero => f Zero\n  Succ k => f k',
        ]
        for definition in definitions:
            with self.subTest(definition=definition):
                result = self.run_source('module Main\nf : (1 n : Nat) -> Nat\n' + definition +
                                         '\nmain : Nat\nmain = Zero\n')
                self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_nat_rejects_recursion_coverage_and_linear_discard(self):
        definitions = [
            'f Zero = Zero\nf Succ n = f n',
            'f Zero = Zero\nf Zero = Zero',
            'f n = case n of\n  Zero => Zero',
            'f Zero = Zero\nf Succ n = Zero',
        ]
        for definition in definitions:
            with self.subTest(definition=definition):
                result = self.run_source('module Main\nf : Nat -> Nat\n' + definition +
                                         '\nmain : Nat\nmain = Zero\n')
                self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_nat_clause_binder_navigation(self):
        source = 'f : Nat -> Nat\nf Zero = Zero\nf Succ n = Succ n\nmain : Nat\nmain = Zero\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            path.write_text(source)
            result = subprocess.run([str(EXE), 'rename-preview', '3', '8', 'item', str(path)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            edits = json.loads(result.stdout)['edits']
            self.assertEqual([(x['range']['start']['line'], x['range']['start']['column'])
                              for x in edits], [(3, 8), (3, 17)])

    def test_clause_headers_navigation_and_rename(self):
        source = "f : Bool -> Bool\nf A = True\nf B = False\nf C z = True\nmain : Bool\nmain = f True\n"
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

    def test_rename_rejects_ambiguous_final_clause_heads(self):
        cases = [
            ("first : Bool\nfirst = True\nsecond : Bool\nsecond = False\nf : Bool -> Bool\nf first = True\nf second = False\nmain : Bool\nmain = True\n", '3', '1', 'other'),
            ("other : Nat\nother = Zero\nf : Nat -> Nat\nf Zero = Zero\nf item = item\nmain : Nat\nmain = other\n", '1', '1', 'item'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            for source, line, column, name in cases:
                with self.subTest(name=name):
                    path.write_text(source)
                    result = subprocess.run([str(EXE), 'rename-preview', line, column, name, str(path)],
                                            text=True, capture_output=True)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn('lexical resolution would change', result.stderr)

    def test_rename_unrelated_name_with_ambiguous_final_head(self):
        source = ('other : Nat\nother = Zero\nf : Nat -> Nat\n'
                  'f Zero = other\nf item = item\nmain : Nat\nmain = other\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            path.write_text(source)
            result = subprocess.run([str(EXE), 'rename-preview', '1', '1', 'value', str(path)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual([edit['range']['start']['line'] for edit in json.loads(result.stdout)['edits']],
                             [1, 2, 4, 7])

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

    def test_final_nat_binder_used_and_unused(self):
        for body, result_type, value, expected in [
            ('item', 'Nat', 'Zero', 'Zero'),
            ('item', 'Nat', 'Succ Zero', '(Succ Zero)'),
            ('False', 'Bool', 'Succ Zero', 'False'),
        ]:
            base = 'Zero' if result_type == 'Nat' else 'True'
            source = ('module Main\nf : Nat -> ' + result_type + '\nf Zero = ' + base +
                      '\nf item = ' + body + '\nmain : ' + result_type +
                      '\nmain = f (' + value + ')\n')
            result = self.run_source(source)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('Normal: ' + expected, result.stdout)

    def test_final_nat_binder_rejects_uppercase_and_linear_input(self):
        for signature, name in [('Nat -> Nat', 'Missing'), ('(1 n : Nat) -> Nat', 'item')]:
            result = self.run_source('module Main\nf : ' + signature + '\nf Zero = Zero\n' +
                                     f'f {name} = Zero\nmain : Nat\nmain = Zero\n')
            self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_final_nat_binder_visible_nonconstructor_is_rejected(self):
        source = ('module Main\nitem : Bool\nitem = True\nf : Nat -> Nat\n'
                  'f Zero = Zero\nf item = Zero\nmain : Nat\nmain = Zero\n')
        self.assertNotEqual(self.run_source(source).returncode, 0)

    def test_imported_candidates_and_catchall_before_zero_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for module in ('First', 'Second'):
                (root / (module + '.fib')).write_text(
                    f'module {module}\nexport\nitem : Bool\nitem = True\n')
            path = root / 'Main.fib'
            for imports, clauses, diagnostic in [
                ('import First\n', 'f Zero = Zero\nf item = Zero', 'Nat-case constructor does not match'),
                ('import First\nimport Second\n', 'f Zero = Zero\nf item = Zero', 'Ambiguous imported name item'),
                ('', 'f item = item\nf Zero = Zero', 'Unbound name "item"'),
            ]:
                with self.subTest(imports=imports, clauses=clauses):
                    path.write_text('module Main\n' + imports + 'f : Nat -> Nat\n' +
                                    clauses + '\nmain : Nat\nmain = Zero\n')
                    result = subprocess.run([str(EXE), 'eval', '--source-dir', directory, str(path)],
                                            text=True, capture_output=True, timeout=20)
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertIn(diagnostic, result.stderr)

    def test_lowercase_constructor_remains_a_constructor(self):
        source = '''module Main
data Choice : Type where
  first : Choice
  second : Choice
f : Choice -> Bool
f first = True
f second = False
main : Bool
main = f second
'''
        result = self.run_source(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Normal: False', result.stdout)

    def test_unresolved_final_head_is_not_a_navigation_binder(self):
        source = 'f : Nat -> Nat\nf Zero = Zero\nf item = item\nmain : Nat\nmain = Zero\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            path.write_text(source)
            result = subprocess.run([str(EXE), 'references', '3', '3', str(path)],
                                    text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['references'], [])

    def test_unresolved_final_head_body_does_not_link_outer_name(self):
        source = ('item : Nat\nitem = Zero\nf : Nat -> Nat\nf Zero = Zero\n'
                  'f item = item\nmain : Nat\nmain = item\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'source.fib'
            path.write_text(source)
            for column in (3, 10):
                result = subprocess.run([str(EXE), 'references', '5', str(column), str(path)],
                                        text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                references = json.loads(result.stdout)['references']
                if column == 10:
                    self.assertEqual(references, [])
                else:
                    self.assertNotIn(5, [span['start']['line'] for span in references
                                         if span['start']['column'] == 10])

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

    COLOR = '''module Main
data Color : Type where
  Red : Color
  Green : Color
  Blue : Color
data Shape : Type where
  Circle : (radius : Nat) -> Shape
  Empty : Shape
'''

    def test_data_catch_all_wildcard_and_name(self):
        cases = [
            ('isRed : Color -> Bool\nisRed Red = True\nisRed other = False', 'isRed Green', 'False'),
            ('isRed : Color -> Bool\nisRed Red = True\nisRed other = False', 'isRed Red', 'True'),
            ('f : Color -> Bool\nf Blue = False\nf _ = True', 'f Green', 'True'),
            ('f : Color -> Bool\nf Blue = False\nf _ = True', 'f Blue', 'False'),
            ('f : Shape -> Bool\nf Empty = True\nf _ = False', 'f (Circle Zero)', 'False'),
            ('f : Shape -> Bool\nf Empty = True\nf _ = False', 'f Empty', 'True'),
            ('f : Shape -> Shape\nf Empty = Empty\nf s = s', 'f (Circle Zero)', 'Inject (Variant  (payload unrestricted Nat) nullary) 0 Zero'),
        ]
        for definition, expression, expected in cases:
            with self.subTest(definition=definition, expression=expression):
                result = self.run_source(self.COLOR + definition + '\nmain : ' +
                                         ('Shape' if 'Shape -> Shape' in definition else 'Bool') +
                                         '\nmain = ' + expression + '\n')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(expected, result.stdout)

    def test_data_catch_all_rejections(self):
        cases = [
            # every constructor already matched
            'f : Color -> Bool\nf Red = True\nf Green = True\nf Blue = True\nf _ = False',
            # a linear payload cannot be dropped by a wildcard
            'f : (1 value : Sum Bool Bool) -> Bool\nf Left x = x\nf _ = True',
            # a catch-all must come last, and must not be followed by a constructor
            'f : Color -> Bool\nf other = True\nf Red = False',
            # the catch-all result must still match the declared type
            'f : Color -> Bool\nf Red = True\nf other = other',
        ]
        for definition in cases:
            with self.subTest(definition=definition):
                result = self.run_source(self.COLOR + DATA.split('\n', 1)[1] + definition + '\nmain : Bool\nmain = True\n')
                self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_nat_wildcard_catch_all(self):
        for value, expected in (('Zero', 'True'), ('Succ Zero', 'False')):
            with self.subTest(value=value):
                result = self.run_source('module Main\nisZero : Nat -> Bool\nisZero Zero = True\nisZero _ = False\n'
                                         'main : Bool\nmain = isZero (' + value + ')\n')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('Normal: ' + expected, result.stdout)

    def test_single_constructor_data_case(self):
        data = 'module Main\ndata Handle : Type where\n  Open : (1 log : String) -> Handle\n'
        ok = self.run_source(data + 'close : (1 h : Handle) -> String\nclose h = case h of Open log => log\n'
                             'main : String\nmain = close (Open "done")\n')
        self.assertEqual(ok.returncode, 0, ok.stderr)
        self.assertIn('done', ok.stdout)
        # the linear payload must still be used exactly once
        leak = self.run_source(data + 'leak : (1 h : Handle) -> String\nleak h = case h of Open log => "dropped"\n'
                               'main : String\nmain = leak (Open "x")\n')
        self.assertNotEqual(leak.returncode, 0, leak.stdout)

if __name__ == '__main__':
    unittest.main()
