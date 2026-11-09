#!/usr/bin/env python3
"""Per-invocation evaluation limits on the native embedding APIs (FNativeLimits).

Real emitted programs are driven through fibril_native_embed_limited and
fibril_native_binary_embed_limited. The harness #defines the call the emitter generates
(`fibril_native_embed(entry, host)`) to the limited variant before including the emitted C, so no
emitter change is needed. Defaults must be unchanged, raising and lowering must take effect, every
limit must stay finite, and usage must be reported on success and on failure.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import unittest

from test_cli import ROOT, run_cli
import test_native_tail as tail

RUNTIME = ROOT / 'runtime/native'
CC = shlex.split(os.environ.get('CC', 'cc'))

CEILING = {'steps': 1073741824, 'depth': 16384, 'bytes': 1073741824}

# natRec over 65536 successors: roughly 1.7M steps and 33 MB allocated, so it needs both raised.
BIG = tail.HEADER + '''main : IO Unit
main = putStrLn (if primWordEq (primWordFromNat (double (double (double (double (double (double (double (double 256))))))))) 65536w then "counted" else "wrong")
'''

TEXT_HARNESS = r'''#include <stdio.h>
#include <stdlib.h>
#include "fibril_runtime.h"
static FNativeLimits g_limits;
static const FNativeLimits *g_use = &g_limits;
#define fibril_native_embed(entry, host) fibril_native_embed_limited((entry), (host), g_use)
#include "program.c"
static int sink_write(void *c, const unsigned char *b, size_t n) { (void)c; return fwrite(b, 1, n, stdout) == n ? 0 : 1; }
static int sink_flush(void *c) { (void)c; return fflush(stdout) == EOF ? 1 : 0; }
int main(int argc, char **argv) {
  if (argc >= 4) { g_limits.steps = strtoull(argv[1], 0, 10); g_limits.depth = strtoull(argv[2], 0, 10); g_limits.bytes = strtoull(argv[3], 0, 10); }
  if (argc >= 5) g_use = NULL;   /* the NULL / unmodified path */
  FNativeHost host = { NULL, sink_write, sink_flush };
  FNativeResult r = fibril_program_embed(&host);
  fprintf(stderr, "status=%d message=%s steps=%zu peak_depth=%zu bytes=%zu\n", (int)r.status, r.message ? r.message : "-",
          r.usage.steps, r.usage.peak_depth, r.usage.bytes);
  return (int)r.status;
}
'''

BINARY_HARNESS = r'''#include <stdio.h>
#include <stdlib.h>
#include "fibril_binary_embed.h"
static FNativeLimits g_limits;
#define fibril_native_binary_embed(entry, requests, capacity, host) \
  fibril_native_binary_embed_limited((entry), (requests), (capacity), (host), &g_limits)
#include "program.c"
static int rd(void *c) { (void)c; return -1; }
static int wr(void *c, unsigned char b) { (void)c; (void)b; return 0; }
static int fl(void *c) { (void)c; return 0; }
int main(int argc, char **argv) {
  if (argc >= 4) { g_limits.steps = strtoull(argv[1], 0, 10); g_limits.depth = strtoull(argv[2], 0, 10); g_limits.bytes = strtoull(argv[3], 0, 10); }
  FByteAdapters host = { rd, wr, fl, NULL };
  FBinaryResult r = fibril_program_binary_embed(&host);
  fprintf(stderr, "status=%d message=%s steps=%zu peak_depth=%zu bytes=%zu\n", (int)r.status, r.message ? r.message : "-",
          r.usage.steps, r.usage.peak_depth, r.usage.bytes);
  return (int)r.status;
}
'''
RESULT = re.compile(rb'status=(\d+) message=(.*) steps=(\d+) peak_depth=(\d+) bytes=(\d+)')


class NativeLimitTests(unittest.TestCase):
    def build(self, source, directory, harness=TEXT_HARNESS, emit='emit-c', runtime_c='fibril_runtime.c'):
        root = Path(directory) / 'src'
        root.mkdir()
        path = root / 'Main.fib'
        path.write_text(source, encoding='utf-8')
        args = ['--source-dir', str(root)] if source.startswith('module ') else []
        emitted = run_cli(emit, *args, str(path), timeout=120)
        self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
        (Path(directory) / 'program.c').write_text(emitted.stdout, encoding='utf-8')
        (Path(directory) / 'harness.c').write_text(harness, encoding='utf-8')
        exe = Path(directory) / 'p'
        build = subprocess.run(CC + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', '-DFIBRIL_EMBED_ONLY',
                                     '-I', str(RUNTIME), '-I', directory, str(Path(directory) / 'harness.c'),
                                     str(RUNTIME / runtime_c), '-o', str(exe)],
                               capture_output=True, text=True, timeout=120)
        self.assertEqual(build.returncode, 0, build.stderr)
        return exe

    def run_exe(self, exe, steps=0, depth=0, bytes_=0, null=False):
        argv = [str(exe), str(steps), str(depth), str(bytes_)] + (['null'] if null else [])
        result = subprocess.run(argv, capture_output=True, timeout=120)
        match = RESULT.search(result.stderr)
        self.assertIsNotNone(match, result.stderr)
        status, message, steps_used, peak, used_bytes = match.groups()
        return dict(status=int(status), message=message.decode(), steps=int(steps_used), depth=int(peak),
                    bytes=int(used_bytes), stdout=result.stdout)

    def test_zero_fields_and_null_keep_every_default(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(tail.HEADER + tail.NON_TAIL, directory)
            for run in (self.run_exe(exe), self.run_exe(exe, null=True)):
                self.assertEqual(run['status'], 2, run)              # F_NATIVE_PROGRAM_ERROR
                self.assertIn('(depth limit)', run['message'])
                self.assertEqual(run['depth'], 512, 'the default depth limit is unchanged')
                self.assertGreater(run['steps'], 0)

    def test_depth_can_be_raised_and_lowered_per_invocation(self):
        with tempfile.TemporaryDirectory() as directory:
            deep = self.build(tail.HEADER + tail.NON_TAIL, directory)
            short = self.run_exe(deep, depth=4096)        # raised, but this recursion needs about 6000
            self.assertIn('(depth limit)', short['message'])
            self.assertEqual(short['depth'], 4096, 'the raised limit is the one enforced')
            ok = self.run_exe(deep, depth=CEILING['depth'])
            self.assertEqual((ok['status'], ok['stdout']), (0, b'counted\n'), ok)
            self.assertTrue(4096 < ok['depth'] <= CEILING['depth'], ok)
            low = self.run_exe(deep, depth=64)
            self.assertIn('(depth limit)', low['message'])
            self.assertEqual(low['depth'], 64)

    def test_tail_loop_fits_a_small_depth_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            run = self.run_exe(self.build(tail.LOOP, directory), depth=64)
            self.assertEqual((run['status'], run['stdout']), (0, b'done\n'), run)
            self.assertLess(run['depth'], 64)

    def test_steps_can_be_lowered_and_raised(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(tail.LOOP, directory)
            low = self.run_exe(exe, steps=1000)
            self.assertIn('(step limit)', low['message'])
            self.assertEqual(low['steps'], 1000, 'stops exactly at the lowered limit')
            self.assertEqual(self.run_exe(exe, steps=200000)['status'], 0)

    def test_bytes_limit_is_enforced_and_can_be_raised(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(tail.LOOP, directory)
            small = self.run_exe(exe, bytes_=4096)
            self.assertIn('allocation budget exhausted', small['message'])
            self.assertLessEqual(small['bytes'], 4096)
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(BIG, directory)
            default = self.run_exe(exe)
            self.assertEqual(default['status'], 2, 'too big for the default limits')
            raised = self.run_exe(exe, steps=4000000, bytes_=100000000)
            self.assertEqual((raised['status'], raised['stdout']), (0, b'counted\n'), raised)
            self.assertGreater(raised['bytes'], 16777216, 'used more than the default allocation limit')
            self.assertGreater(raised['steps'], 100000, 'used more than the default step limit')

    def test_every_limit_stays_finite(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.build(tail.LOOP, directory)
            for name in CEILING:
                args = dict(steps=0, depth=0, bytes_=0)
                key = 'bytes_' if name == 'bytes' else name
                args[key] = CEILING[name] + 1
                run = self.run_exe(exe, **args)
                self.assertEqual(run['status'], 1, (name, run))      # F_NATIVE_INVALID_ARGUMENT
                self.assertIn('above its ceiling', run['message'])
                self.assertEqual((run['steps'], run['stdout']), (0, b''), 'nothing ran')
            ok = self.run_exe(exe, depth=CEILING['depth'])
            self.assertEqual(ok['status'], 0, 'a value exactly at the ceiling is accepted')

    def test_usage_is_reported_on_success_and_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            ok = self.run_exe(self.build(tail.LOOP, directory), null=True)
            self.assertEqual(ok['status'], 0)
            self.assertTrue(ok['steps'] > 2048 and ok['depth'] > 0 and ok['bytes'] > 0, ok)

    def test_binary_embedding_takes_limits_too(self):
        with tempfile.TemporaryDirectory() as directory:
            source = (ROOT / 'examples/core/binary-echo.fib').read_text()
            exe = self.build(source, directory, BINARY_HARNESS, emit='emit-c-binary', runtime_c='fibril_binary_runtime.c')
            default = self.run_exe(exe)
            self.assertEqual(default['status'], 0, default)           # F_BINARY_OK
            self.assertTrue(default['steps'] > 0 and default['depth'] > 0, default)
            starved = self.run_exe(exe, steps=0, depth=2)
            self.assertEqual(starved['status'], 2, starved)           # F_BINARY_PROGRAM_ERROR
            self.assertIn('(depth limit)', starved['message'])
            self.assertEqual(starved['depth'], 2)
            self.assertEqual(self.run_exe(exe, depth=CEILING['depth'] + 1)['status'], 1)   # INVALID_ARGUMENT


if __name__ == '__main__':
    unittest.main()
