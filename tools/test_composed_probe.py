#!/usr/bin/env python3
"""Measurement boundary tests; no timing regression thresholds."""
from pathlib import Path
import shlex
import os
import sys
import tempfile
import unittest

from probe_composed import ROOT, EXE, timed, native, extract_profile, replace_once, required


class ComposedProbeTests(unittest.TestCase):
    def test_nonzero_exit_keeps_output_and_individual_rss(self):
        result = timed([sys.executable, '-c',
            'import sys; print("kept"); print("refusal", file=sys.stderr); sys.exit(23)'])
        self.assertEqual(result['returncode'], 23)
        self.assertEqual(bytes.fromhex(result['stdout_hex']), b'kept\n')
        self.assertEqual(result['stderr'], 'refusal\n')
        self.assertGreater(result['peak_rss_bytes'], 0)
        self.assertEqual(result['outcome'], 'rejected')

    def test_deadline_is_not_a_success_or_a_memory_measurement(self):
        result = timed([sys.executable, '-c', 'import time; time.sleep(10)'], timeout=1)
        self.assertEqual(result['outcome'], 'timeout')
        self.assertIsNone(result['peak_rss_bytes'])
        self.assertIsNone(result['returncode'])

    def test_changed_observer_anchors_fail_closed(self):
        for source in ('absent', 'anchor anchor'):
            with self.assertRaises(ValueError):
                replace_once(source, 'anchor', 'changed')

    def test_missing_and_duplicate_profiles_fail_closed(self):
        for diagnostic in ('', 'COMPOSED {}\nCOMPOSED {}\n'):
            with self.assertRaises(ValueError):
                extract_profile({'outcome': 'success', 'stderr': diagnostic})

    def test_private_counters_match_plain_success_and_budget_failure(self):
        cc = shlex.split(os.environ.get('CC', 'cc'))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'Main.fib'
            path.write_text('module Main\ngreeting : String\ngreeting = "ok"\n'
                            'main : IO Unit\nmain = putStrLn greeting\n')
            success = required([EXE, 'emit-c', '--source-dir', root, path]).encode()
            # Trusted C injection exercises failure observation, not source admission.
            failure = b'#include "fibril_runtime.h"\nstatic FValue *loop(FRuntime *r, FEnv *e) { (void)e; return f_global(r, loop); }\nint main(void) { return fibril_native_run(loop); }\n'
            for index, code in enumerate((success, failure)):
                plain = native(root / f'plain-{index}', code, False, cc, False)
                observed = native(root / f'observed-{index}', code, False, cc, True)
                baseline = timed([plain])
                actual = timed([observed])
                profile = extract_profile(actual)
                for field in ('outcome', 'returncode', 'stdout_hex', 'stderr'):
                    self.assertEqual(actual[field], baseline[field])
                self.assertGreater(profile['global_calls'], 0)
                self.assertGreater(profile['steps'], 0)
                if index == 0:
                    self.assertEqual(profile['peak_arena_payload'],
                        sum(pair[1] for pair in profile['allocations'].values()))
                    self.assertEqual(bytes.fromhex(actual['stdout_hex']), b'ok\n')
                else:
                    self.assertEqual(profile['peak_depth'], 512)
                    self.assertEqual(actual['outcome'], 'rejected')


if __name__ == '__main__':
    unittest.main()
