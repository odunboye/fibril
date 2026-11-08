#!/usr/bin/env python3
"""Construction reservations must stay bounded and emitted syntax cumulative."""
import tempfile
import os
import shlex
from pathlib import Path
import unittest

from probe_construction import instrument, validate_ledger
from probe_composed import native
from probe_lsp_cost_audit import prepare_root
from test_cli import run_cli


class ConstructionTests(unittest.TestCase):
    def test_ledger_reclaims_only_unused_reservation(self):
        ledger = [{'event': 'reserve', 'name': 'A.first', 'remaining': 200000, 'full_estimate': 150000},
                  {'event': 'built', 'name': 'A.first', 'nodes': 3},
                  {'event': 'reserve', 'name': 'B.second', 'remaining': 199997, 'full_estimate': 180000},
                  {'event': 'built', 'name': 'B.second', 'nodes': 4},
                  {'event': 'finish', 'name': 'B', 'remaining': 199993}]
        summary = validate_ledger(ledger, 'RESULT accepted 7 8', True)
        self.assertEqual(summary['remaining'], 199993)
        self.assertEqual(summary['maximum_retained_plus_active_reservation'], 180003)
        with self.assertRaises(ValueError):
            validate_ledger(ledger, 'RESULT accepted 7 8', False)

    def test_bad_size_or_cross_module_reset_cannot_reconcile(self):
        for ledger in (
            [{'event': 'reserve', 'name': 'A.x', 'remaining': 200000, 'full_estimate': 2},
             {'event': 'built', 'name': 'A.x', 'nodes': 3}],
            [{'event': 'reserve', 'name': 'A.x', 'remaining': 200000, 'full_estimate': 3},
             {'event': 'built', 'name': 'A.x', 'nodes': 3},
             {'event': 'reserve', 'name': 'B.x', 'remaining': 200000, 'full_estimate': 2}],
            [{'event': 'reserve', 'name': 'A.x', 'remaining': 200000, 'full_estimate': 3},
             {'event': 'built', 'name': 'A.x', 'nodes': 3},
             {'event': 'finish', 'name': 'A', 'remaining': 200000}],
        ):
            with self.assertRaises(ValueError):
                validate_ledger(ledger, 'RESULT rejected', True)

    def test_observer_anchor_changes_fail_closed(self):
        with self.assertRaises(ValueError):
            instrument('module Fibril.Driver.ModuleCheck\n')

    def test_json_then_typed_checks_and_emits_without_visibility_bypass(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = prepare_root(Path(temporary))
            entry = root / 'JSONThenTyped.fib'
            for command in ('check', 'emit-c-binary'):
                result = run_cli(command, '--source-dir', str(root), str(entry), timeout=120)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            # Compile the emitted program, without presenting the fixed-input
            # admission probe as a wire pipeline or executing it as one.
            target = native(Path(temporary) / 'compiled', result.stdout.encode(), True,
                            shlex.split(os.environ.get('CC', 'cc')), False)
            self.assertTrue(target.is_file())
            blocked = run_cli('emit-c-binary', '--source-dir', str(root), str(root / 'EchoJSONThenTyped.fib'), timeout=120)
            self.assertNotEqual(blocked.returncode, 0)
            self.assertEqual(blocked.stdout, '')
            self.assertIn('Unbound name "JSONThenTyped.main"', blocked.stderr)
            # An explicitly exported test copy gets past visibility; the larger
            # graph must still fail the independent, unchanged native gate.
            entry.write_text(entry.read_text().replace('main : IO Unit', 'export\nmain : IO Unit'))
            combined = root / 'EchoJSONThenTyped.fib'
            checked = run_cli('check', '--source-dir', str(root), str(combined), timeout=120)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
            bounded = run_cli('emit-c-binary', '--source-dir', str(root), str(combined), timeout=120)
            self.assertNotEqual(bounded.returncode, 0)
            self.assertEqual(bounded.stdout, '')
            self.assertIn('Native core admission exceeds 8192 nodes', bounded.stderr)

    def test_conservative_declarations_share_budget_across_modules(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for module in ('One', 'Two'):
                lines = [f'module {module}', 'data Choice : Type where', '  A : Choice', '  B : Choice']
                for index in range(12):
                    lines += [f'choose{index} : Choice -> Bool',
                              f'choose{index} value = case value of', '  A => True', '  B => False']
                (root / (module + '.fib')).write_text('\n'.join(lines) + '\n')
            entry = root / 'Main.fib'
            entry.write_text('module Main\nimport One\nimport Two\nmain : IO Unit\nmain = putStrLn "ok"\n')
            result = run_cli('run', '--source-dir', str(root), str(entry), timeout=120)
            self.assertEqual((result.returncode, result.stdout), (0, 'ok\n'), result.stderr)
            # A private, unused bad declaration is still independently checked.
            with (root / 'Two.fib').open('a') as stream:
                stream.write('bad : Bool\nbad = "wrong"\n')
            rejected = run_cli('run', '--source-dir', str(root), str(entry), timeout=120)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')

    def test_emitted_footprint_is_cumulative_even_for_unused_private_globals(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            # A literal's actual successor chain remains in its stored body.
            # These definitions have no motive/inference reservation inflation.
            for index in range(14):
                declarations = ''.join(f'v{n} : Nat\nv{n} = 256\n' for n in range(60))
                (root / f'M{index}.fib').write_text(f'module M{index}\n' + declarations)
            entry = root / 'Main.fib'
            def main(count):
                entry.write_text('module Main\n' + ''.join(f'import M{i}\n' for i in range(count)) +
                                 'main : IO Unit\nmain = putStrLn "ok"\n')
            main(12)
            accepted = run_cli('check', '--source-dir', str(root), str(entry), timeout=120)
            self.assertEqual(accepted.returncode, 0, accepted.stdout + accepted.stderr)
            main(14)
            rejected = run_cli('run', '--source-dir', str(root), str(entry), timeout=120)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(rejected.stdout, '')
            self.assertIn('Expanded core construction budget exhausted (200000)', rejected.stderr)

    def test_oversized_single_reservation_still_refuses_before_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'Main.fib'
            text = 'module Main\ndata Choice : Type where\n  A : Choice\n  B : Choice\nchoose : Choice -> Bool\nchoose value = case value of\n'
            depth = 12
            for level in range(depth):
                text += ' ' * (2 * (level + 1)) + 'A => case value of\n'
            text += ' ' * (2 * (depth + 1)) + 'A => True\n'
            text += ' ' * (2 * (depth + 1)) + 'B => False\n'
            for level in reversed(range(depth)):
                text += ' ' * (2 * (level + 1)) + 'B => False\n'
            path.write_text(text + 'main : IO Unit\nmain = putStrLn "never"\n')
            result = run_cli('run', '--source-dir', str(root), str(path), timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertIn('Expanded core construction budget exhausted (200000)', result.stderr)


if __name__ == '__main__':
    unittest.main()
