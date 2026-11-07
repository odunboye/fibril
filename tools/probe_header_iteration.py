#!/usr/bin/env python3
"""Observe checked Fibril header-iteration diagnostics, NOT a production parser.

Controls are generated from the preserved source. The classification control
INTENTIONALLY removes ASCII validation/casefolding: it is cost attribution only.
No parser or runtime budget implementation lives in this process client. Exit
zero means observations completed, NOT that budget-blocked cases succeeded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import tempfile

from probe_header_loops import ROOT, invoke, report

FIXTURE = ROOT / 'tools/fixtures/header-iteration/names'
VARIANTS = ('baseline', 'classification-control', 'aliases', 'aliases-classification-control', 'value-first')
METRICS = r'''
#define fibril_native_binary_run uninstrumented_binary_run
#include "fibril_binary_runtime.c"
#undef fibril_native_binary_run
static size_t requests_used, capacity_used, consumed, accepted, flushes;
static int counted_read(void *unused) {
  (void)unused;
  int c = fgetc(stdin);
  if(c != EOF) { consumed++; return c; }
  return ferror(stdin) ? -2 : -1;
}
static int counted_write(void *unused, unsigned char c) {
  (void)unused;
  if(fputc(c,stdout) == EOF) return -1;
  accepted++; return 0;
}
static int counted_flush(void *unused) {
  (void)unused; flushes++;
  return fflush(stdout) == 0 ? 0 : -1;
}
static FByteStatus counted_body(FByteSession *session,void *context) {
  size_t requests=session->requests,capacity=session->capacity;
  FByteStatus status=binary_body(session,context);
  requests_used=requests-session->requests;
  capacity_used=capacity-session->capacity;
  return status;
}
int fibril_native_binary_run(FEval entry,size_t requests,size_t capacity) {
  FRuntime runtime={0};
  FBinaryContext context={&runtime,entry,FB_OK,0,0};
  FByteAdapters host={counted_read,counted_write,counted_flush,NULL};
  FByteStatus status=fibril_bytes_run_with(requests,capacity,host,counted_body,&context);
  size_t allocations=0;
  for(FAllocation *p=runtime.allocations;p;p=p->next) allocations++;
  fprintf(stderr,"HEADER_LOOP_METRICS %zu %zu %zu %zu\n",
    runtime.steps,runtime.bytes,F_MAX_STEPS,F_MAX_DEPTH);
  fprintf(stderr,"HEADER_ITERATION_METRICS %zu %zu %zu %zu %zu %zu %zu %zu %zu %zu\n",
    probe_peak,probe_callbacks,probe_reads,probe_writes,allocations,
    requests_used,capacity_used,consumed,accepted,flushes);
  return binary_finish(&runtime,&context,status);
}
'''


def replace_exact(text, old, new, count=1):
    if text.count(old) != count:
        raise ValueError(f'changed source/observer seam: {old!r}')
    return text.replace(old, new)


def source_variant(source, variant):
    if variant not in VARIANTS:
        raise ValueError(variant)
    if 'classification-control' in variant:
        start = source.index('  let (lower : ')
        end = source.index('\n', start)
        source = source[:start] + '  let (lower : (bytes : Bytes) -> String) = \\(bytes : Bytes) => ascii bytes in' + source[end:]
    if variant.startswith('aliases') or variant == 'value-first':
        marker = '  let (respond : '
        start = source.index(marker)
        aliases = '''  let (read : IO ByteReadResult) = primReadBytes one in
  let (readBind : (1 action : IO ByteReadResult) -> (1 next : (1 response : ByteReadResult) -> IO (LoopStep S Bytes)) -> IO (LoopStep S Bytes)) = primBind ByteReadResult (LoopStep S Bytes) in
  let (readCase : (1 response : ByteReadResult) -> (eof : IO (LoopStep S Bytes)) -> (chunk : (1 bytes : Bytes) -> IO (LoopStep S Bytes)) -> IO (LoopStep S Bytes)) = primByteReadCase (IO (LoopStep S Bytes)) in
  let (continue : (1 state : S) -> LoopStep S Bytes) = primLoopContinue S Bytes in
  let (done : (1 header : Bytes) -> LoopStep S Bytes) = primLoopDone S Bytes in
'''
        source = source[:start] + aliases + source[start:]
        source = source.replace('(primLoopContinue S Bytes (scan phase name lines saved))', '(continue (scan phase name lines saved))')
        source = source.replace('(primLoopDone S Bytes primBytesEmpty)', '(done primBytesEmpty)')
        source = source.replace('(primLoopDone S Bytes next)', '(done next)')
        source = replace_exact(source,
            'bind ByteReadResult (LoopStep S Bytes) (primReadBytes one)', 'readBind read')
        source = replace_exact(source,
            'primByteReadCase (IO (LoopStep S Bytes)) r', 'readCase r')
    if variant == 'value-first':
        value = r'''if same c "\r" then more "lf" name lines next else
        let (folded : String) = lower raw in
        if orBool (same folded "") (same folded "\t") then reject else more "value" name lines next'''
        # Keep the original fallback too; only hot dispatch ordering changes.
        source = replace_exact(source, '      if same phase "end" then',
            '      if same phase "value" then ' + value + ' else\n      if same phase "end" then')
    return source


def instrument(work):
    for path in (ROOT / 'runtime/native').iterdir():
        if path.is_file():
            shutil.copyfile(path, work / path.name)
    path = work / 'fibril_runtime.c'
    text = replace_exact(path.read_text(), 'static int enter(FRuntime *r) {',
        'static size_t probe_peak,probe_callbacks,probe_reads,probe_writes;\nstatic int enter(FRuntime *r) {')
    text = replace_exact(text, 'r->steps++; r->depth++; return 1;',
        'r->steps++; r->depth++; if(r->depth>probe_peak) probe_peak=r->depth; return 1;')
    path.write_text(text)
    path = work / 'fibril_binary_runtime.c'
    text = replace_exact(path.read_text(), 'apply_thunk(r, step, input)',
        '(probe_callbacks++, apply_thunk(r, step, input))', count=2)
    text = replace_exact(text, 'FByteRead read = fibril_bytes_read(session, capacity);',
        'probe_reads++; FByteRead read = fibril_bytes_read(session, capacity);')
    text = replace_exact(text, 'FByteStatus status = fibril_bytes_write(session,',
        'probe_writes++; FByteStatus status = fibril_bytes_write(session,')
    path.write_text(text)


def native_metrics(stderr):
    names = ('peak_pure_depth', 'callbacks', 'reads', 'writes', 'arena_allocations',
             'requests', 'reserved_capacity', 'consumed_bytes', 'accepted_bytes', 'flushes')
    rows = re.findall(rb'^HEADER_ITERATION_METRICS ([0-9 ]+)$', stderr, re.MULTILINE)
    if len(rows) != 1 or len(rows[0].split()) != len(names):
        raise ValueError('missing or malformed native observer metrics')
    return dict(zip(names, map(int, rows[0].split())))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fibril', type=Path, default=ROOT / 'build/exec/fibril')
    parser.add_argument('--measure', type=Path, help='optional worktree-private Measure.idr executable')
    parser.add_argument('--variants', default=','.join(VARIANTS))
    parser.add_argument('--sizes', default='20,128,1024')
    parser.add_argument('--timeout', type=int, default=30)
    args = parser.parse_args()
    variants = args.variants.split(',')
    sizes = list(map(int, args.sizes.split(',')))
    if (not set(variants) <= set(VARIANTS) or len(variants) > len(VARIANTS) or not sizes or
            len(sizes) > 8 or any(n < 6 or n > 1025 for n in sizes) or not 1 <= args.timeout <= 120):
        parser.error('invalid variants, sizes (6..1025, at most8), or timeout (1..120)')
    failed = False
    source = (FIXTURE / 'Main.fib').read_text()
    with tempfile.TemporaryDirectory(prefix='fibril-header-iteration-') as temporary:
        for variant in variants:
            work = Path(temporary) / variant
            work.mkdir()
            path = work / 'Main.fib'
            generated = source_variant(source, variant)
            if variant == 'value-first' and generated != (FIXTURE.parent / 'value-first/Main.fib').read_text():
                raise ValueError('preserved value-first fixture differs from source specialization')
            path.write_text(generated)
            print(json.dumps(dict(variant=variant, source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                classification_policy='INTENTIONALLY WEAKENED diagnostic' if 'classification-control' in variant else 'preserved baseline')), flush=True)
            project = ['--source-dir', str(work), str(path)]
            commands = [('check', [str(args.fibril.resolve()), 'check', *project])]
            if args.measure:
                commands.append(('measure', [str(args.measure.resolve()), str(work), str(path)]))
            commands.append(('emit', [str(args.fibril.resolve()), 'emit-c-binary', *project]))
            for phase, command in commands:
                result = invoke(command, timeout=args.timeout)
                failed |= bool(report(variant, phase, command, result)) or result[0] != 0
                if result[0] != 0 or result[3]:
                    return 1
                if phase == 'measure':
                    print(json.dumps(dict(variant=variant, admission=result[1].decode().strip())), flush=True)
                if phase == 'emit':
                    (work / 'main.c').write_bytes(result[1])
            instrument(work)
            (work / 'metrics.c').write_text(METRICS)
            command = shlex.split(os.environ.get('CC', 'cc')) + ['-std=c11', '-Wall', '-Wextra', '-Werror',
                '-I', str(work), str(work / 'main.c'), str(work / 'metrics.c'), '-o', str(work / 'native')]
            result = invoke(command, timeout=90)
            failed |= bool(report(variant, 'cc-observer', command, result)) or result[0] != 0
            if result[0] != 0 or result[3]:
                return 1
            for n in sizes:
                data = b'X:' + b'a' * (n - 6) + b'\r\n\r\n'
                for backend, command in [('hosted', [str(args.fibril.resolve()), 'run-binary', *project]),
                                         ('native', [str(work / 'native')])]:
                    result = invoke(command, data, timeout=args.timeout, open_stdin=True)
                    failed |= bool(report(variant, backend, command, result, expected=data, input_bytes=n,
                        stdin_kept_open=True))
                    if backend == 'native' and not result[3]:
                        print(json.dumps(dict(variant=variant, phase='native-metrics', input_bytes=n,
                            **native_metrics(result[2]))), flush=True)
                    if b'Sanitizer' in result[2] or b'runtime error:' in result[2]:
                        failed = True
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
