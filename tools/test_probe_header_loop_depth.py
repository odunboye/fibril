#!/usr/bin/env python3
"""Observer seam tests; these do not assert current loop failures are permanent."""
from pathlib import Path
import shutil
import tempfile
import unittest

from probe_header_loop_depth import ROOT, instrument, replace_once, trace_generated


class HeaderLoopDepthProbeTests(unittest.TestCase):
    def test_trace_generated_preserves_body_with_variant_array(self):
        body = ' return f_variant_case(r, e, fibril_expr_1, 2, (FEval[]){fibril_expr_2,fibril_expr_3}); '
        source = '#include "fibril_runtime.h"\nstatic FValue *fibril_expr_0(FRuntime *r, FEnv *e) {' + body + '}\n'
        traced = trace_generated(source)
        self.assertIn('void header_probe_expression(FRuntime *, const char *);', traced)
        self.assertIn(body + '}\n', traced)
        self.assertEqual(traced.count('header_probe_expression(r,'), 1)
        self.assertIn('fibril_expr_0 return f_variant_case', traced)

    def test_observer_seams_fail_closed(self):
        for text in ('absent', 'seam seam'):
            with self.assertRaises(ValueError):
                replace_once(text, 'seam', 'replacement')
        with self.assertRaises(ValueError):
            trace_generated('unexpected generated format')

    def test_instrument_only_private_copy_and_keep_limits(self):
        original = (ROOT/'runtime/native/fibril_runtime.c').read_text()
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name in ('fibril_runtime.c', 'fibril_binary_runtime.c'):
                shutil.copyfile(ROOT/'runtime/native'/name, directory/name)
            instrument(directory)
            observed = (directory/'fibril_runtime.c').read_text()
            self.assertEqual([line for line in original.splitlines() if line.startswith('#define F_MAX_')],
                             [line for line in observed.splitlines() if line.startswith('#define F_MAX_')])
            self.assertIn('probe_dump(r); fail(r, r->depth >= LIMIT_DEPTH(r) ? "native evaluation budget exhausted (depth limit)"', observed)
            self.assertIn('probe_peak_depth = r->depth;', observed)
        self.assertEqual((ROOT/'runtime/native/fibril_runtime.c').read_text(), original)


if __name__ == '__main__':
    unittest.main()
