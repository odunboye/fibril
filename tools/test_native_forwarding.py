#!/usr/bin/env python3
"""Forwarded lazy cells versus ordinary application, including region ownership.

Trusted C probes exercise runtime failure boundaries; they are not source
admission evidence. The separate source case goes through the compiler.
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
HARNESS = r'''
#include "fibril_runtime.h"
#include <stdlib.h>
static int forwarding, scenario, ticks;
static FValue *literal(FRuntime *r, FEnv *e) {
  static const unsigned char text[] = {'o','k'}; (void)e;
  ticks++; return f_literal(r, text, sizeof(text));
}
static FValue *constant(FRuntime *r, FEnv *e) {
  static const unsigned char text[] = {'o','k'}; (void)e;
  return f_literal(r, text, sizeof(text));
}
static FValue *bomb(FRuntime *r, FEnv *e) { ticks++; return f_variable(r, e, 999); }
static FValue *var0(FRuntime *r, FEnv *e) { return f_variable(r, e, 0); }
static FValue *argument(FRuntime *r, FEnv *e) {
  return f_variable(r, e, scenario == 2 ? 999 : (scenario == 3 || scenario == 4 ? 1 : 0));
}
static FValue *identity(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, var0); }
static FValue *ignored(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, constant); }
static FValue *erased(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, constant); }
static FValue *duplicate_body(FRuntime *r, FEnv *e) { return f_append(r, e, var0, var0); }
static FValue *duplicate(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, duplicate_body); }
static FValue *unit(FRuntime *r, FEnv *e) { (void)e; return f_unit(r); }
static FValue *call(FRuntime *r, FEnv *e) {
  FEval fn = scenario == 0 ? duplicate : (scenario == 1 || scenario == 5 ? ignored :
             (scenario == 2 ? erased : (scenario == 7 ? unit : identity)));
  size_t index = scenario == 2 ? 999 : (scenario == 3 || scenario == 4 ? 1 : 0);
  return forwarding ? f_apply_variable(r, e, fn, index) : f_apply(r, e, fn, argument);
}
static FValue *nested(FRuntime *r, FEnv *e) { return f_lambda(r, e, 0, call); }
static FValue *region(FRuntime *r, FEnv *e) { return f_lambda(r, e, 1, call); }
static FValue *outer_body(FRuntime *r, FEnv *e) {
  if (scenario == 3) return f_apply(r, e, nested, unit);
  if (scenario == 4) {
    /* The parent's argument is first forced inside the child arena. */
    if (!f_with_region(r, e, region)) return NULL;
    return f_append(r, e, var0, var0);
  }
  return call(r, e);
}
static FValue *outer(FRuntime *r, FEnv *e) {
  return f_lambda(r, e, scenario == 5 || scenario == 6, outer_body);
}
static FValue *text(FRuntime *r, FEnv *e) {
  return f_apply(r, e, outer, scenario == 1 || scenario == 2 || scenario >= 5 ? bomb : literal);
}
static FValue *entry(FRuntime *r, FEnv *e) { return f_write(r, e, text); }
int main(int argc, char **argv) {
  if (argc != 3) return 2;
  forwarding = atoi(argv[1]); scenario = atoi(argv[2]);
  int status = fibril_native_run(entry);
  int expected = scenario == 0 || scenario == 3 || scenario == 4;
  return ticks == expected ? status : 3;
}
'''


class NativeForwardingTests(unittest.TestCase):
    def test_runtime_matches_ordinary_application_with_sanitizers(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / 'harness.c'
            source.write_text(HARNESS)
            target = root / 'harness'
            compiled = subprocess.run(CC + ['-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
                '-pedantic', '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g',
                '-I', str(RUNTIME), str(source), str(RUNTIME / 'fibril_runtime.c'), '-o', str(target)],
                capture_output=True, timeout=120)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            for scenario in range(8):
                with self.subTest(scenario=scenario):
                    results = [subprocess.run([str(target), str(mode), str(scenario)],
                        capture_output=True, timeout=20) for mode in (0, 1)]
                    expected_status = 1 if scenario >= 6 else 0
                    expected = b'okok\n' if scenario in (0, 4) else b'ok\n'
                    for result in results:
                        self.assertEqual(result.returncode, expected_status, result.stderr)
                        self.assertEqual(result.stdout, b'' if expected_status else expected)
                    self.assertEqual(results[0].stderr, results[1].stderr)

    def test_checked_source_emits_forwarding_and_matches_hosted(self):
        source = ('module Main\n'
            'identity : (1 value : String) -> String\nidentity value = value\n'
            'twice : String -> IO Unit\ntwice value = do\n'
            '  putStrLn (primWithRegion String (\\(0 region : Type) => identity value))\n'
            '  putStrLn (identity value)\n'
            'main : IO Unit\nmain = twice (appendString "parent" "!")\n')
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / 'Main.fib'
            path.write_text(source)
            args = ['--source-dir', str(root), str(path)]
            hosted = run_cli('run', *args, text=False, timeout=120)
            self.assertEqual((hosted.returncode, hosted.stdout), (0, b'parent!\nparent!\n'), hosted.stderr)
            emitted = run_cli('emit-c', *args, timeout=120)
            self.assertEqual(emitted.returncode, 0, emitted.stderr)
            self.assertIn('f_apply_variable(', emitted.stdout)
            program = root / 'program.c'
            program.write_text(emitted.stdout)
            target = root / 'program'
            compiled = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror',
                '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g', '-I', str(RUNTIME),
                str(program), str(RUNTIME / 'fibril_runtime.c'), '-o', str(target)], capture_output=True, timeout=120)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            result = subprocess.run([str(target)], capture_output=True, timeout=20)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (0, hosted.stdout, b''))


if __name__ == '__main__':
    unittest.main()
