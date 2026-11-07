#!/usr/bin/env python3
"""Checked-source count-entry safety; raw policy/boundary proofs are separate.

Uses the established private .ipkg and worktree-local package staging from the
iteration suite. Rejections here are count-work results, not parser requirements.
"""
import re
import shutil
import unittest
import test_binary_iteration as iteration


class BinaryCountSafety(unittest.TestCase):
    setUpClass = classmethod(iteration.BinaryIteration.setUpClass.__func__)
    tearDownClass = classmethod(iteration.BinaryIteration.tearDownClass.__func__)
    source = iteration.BinaryIteration.source
    both = iteration.BinaryIteration.both

    def with_count(self, expression):
        original = 'primBytesLength (encode "' + 'x' * 32 + '")'
        self.assertEqual(self.template.count(original), 1)
        return self.source(self.template.replace(original, expression))

    def test_raw_core_policy_boundaries(self):
        directory = self.work / 'core'
        (directory / 'Tests').mkdir(parents=True)
        shutil.copyfile(iteration.ROOT / 'test/src/Tests/BinaryCount.idr', directory / 'Tests/BinaryCount.idr')
        (directory / 'CoreChecks.idr').write_text('''module CoreChecks
import Data.List
import System
import Tests.BinaryCount
main : IO ()
main = do
  traverse_ (\\(name, ok) => putStrLn ((if ok then "PASS " else "FAIL ") ++ name)) checks
  if all snd checks then pure () else exitFailure
''')
        (directory / 'corechecks.ipkg').write_text('package count-core-checks\nsourcedir = "."\ndepends = fibril\nmodules = Tests.BinaryCount, CoreChecks\nmain = CoreChecks\nexecutable = corechecks\n')
        iteration.checked(self.compiler + ['--build', 'corechecks.ipkg'], cwd=directory, env=self.environment)
        result = iteration.checked([directory / 'build/exec/corechecks'])
        self.assertEqual(len(result.stdout.splitlines()), 22, result.stdout)
        self.assertNotIn(b'FAIL', result.stdout)
        print(result.stdout.decode(), end='', flush=True)

    def test_nested_preallocation_denial_before_any_effect(self):
        large = 'primBytesLength (encode "' + 'x' * 5000 + '")'
        derived = 'let (chunk : Bytes) = encode "' + 'x' * 2500 + '" in primBytesLength (primBytesAppend chunk chunk)'
        cases = {
            'direct': large,
            'beta': '(\\(1 raw : Bytes) => primBytesLength raw) (encode "' + 'x' * 5000 + '")',
            'successor': 'Succ (' + large + ')',
            'NatRec': 'natRec (\\(0 n : Nat) => Nat) Zero (\\(0 n : Nat) => \\(1 r : Nat) => Succ r) (' + large + ')',
            'derived-bytes': '(' + derived + ')',
            'full-octet-operand': 'primBytesLength (primBytesOctetMod256 (' + large + '))',
            'full-index-operand': 'primBytesIndexCase Nat (primBytesIndex (' + large + ') (encode "a")) Zero (\\(1 n : Nat) => n)',
            'full-slice-operand': 'primBytesLength (primBytesSlice Zero (' + large + ') (encode "a"))',
            'full-length-is-operand': 'if primBytesLengthIs (' + large + ') primBytesEmpty then Succ Zero else Succ Zero',
        }
        for name, expression in cases.items():
            with self.subTest(path=name):
                directory = self.with_count(expression)
                hosted, native = self.both(directory)
                self.assertFalse(hosted[1], hosted[2])
                self.assertEqual(hosted[0], (0, 0, 0, 1, 0), hosted[2])
                self.assertIn('reduction budget exhausted', hosted[2])
                # Source checking and emission succeeded; budgets are not equal.
                # Native is unchanged and can decode these finite larger counts.
                self.assertNotIn('native evaluation budget exhausted', native[2])

    def test_materialization_and_visits_share_remaining_ledger(self):
        # 2048 fits the old visit-only allowance but construction+visits+the
        # contraction cannot fit4096. This is a work boundary, NOT a count cap.
        directory = self.with_count('primBytesLength (encode "' + 'x' * 2048 + '")')
        hosted, native = self.both(directory)
        self.assertFalse(hosted[1], hosted[2])
        self.assertEqual(hosted[0], (0, 0, 0, 1, 0), hosted[2])
        self.assertIn('reduction budget exhausted', hosted[2])
        self.assertTrue(native[1], native[2])

    def test_zero_small_1024_and_index_payload_counts(self):
        indexed = 'primBytesIndexCase Nat (primBytesIndex Zero (primBytesOctetMod256 (primBytesLength (encode "' + 'x' * 255 + '")))) Zero (\\(1 n : Nat) => n)'
        for expression in ('Succ Zero', 'primBytesLength primBytesEmpty',
                'primBytesLength (encode "' + 'x' * 1024 + '")', indexed):
            directory = self.with_count(expression)
            for backend, (metrics, ok, text) in enumerate(self.both(directory)):
                if expression == 'primBytesLength primBytesEmpty':
                    self.assertFalse(ok, text)
                    self.assertIn('program rejected input', text)
                    self.assertEqual(metrics, (0, 0, 0, 1, 0), text)
                else:
                    self.assertTrue(ok, text)
                    self.assertEqual(metrics, (1, backend, 1, 0, 0), text)

    def test_unused_large_count_branches_and_beta_arguments_stay_lazy(self):
        large = 'primBytesLength (encode "' + 'x' * 5000 + '")'
        for expression in ('if True then Succ Zero else ' + large,
                '(\\(0 unused : Nat) => Succ Zero) (' + large + ')'):
            directory = self.with_count(expression)
            for backend, (metrics, ok, text) in enumerate(self.both(directory)):
                self.assertTrue(ok, text)
                self.assertEqual(metrics, (1, backend, 1, 0, 0), text)
            native = self.both(directory)[1][2]
            self.assertEqual(int(re.search(r'NATIVE \d+ \d+ \d+ (\d+)', native)[1]), 1)


if __name__ == '__main__':
    unittest.main()
