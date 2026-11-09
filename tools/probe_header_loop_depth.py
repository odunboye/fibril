#!/usr/bin/env python3
"""Trace a private runtime copy; never change production evaluation/budget policy.

Only observer calls/counters are inserted. Generated source is checked by the
supplied compiler. Stack rows identify emitted evaluator expressions, not C
backtraces. No parser/iteration implementation lives in this probe.
"""
import argparse
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import tempfile

from probe_header_loops import FIXTURES, METRICS, ROOT, invoke, report


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f'observer seam changed: {old!r}')
    return text.replace(old, new)


def instrument(directory):
    source = directory/'fibril_runtime.c'
    text = source.read_text()
    text = replace_once(text, 'static int enter(FRuntime *r) {', r'''
static const char *probe_stack[512];
static size_t probe_binds, probe_pures, probe_reads, probe_last_read_steps, probe_peak_depth;
static int probe_dumped;
void header_probe_expression(FRuntime *r, const char *description) {
  if (r->depth && r->depth <= 512) probe_stack[r->depth - 1] = description;
}
static void probe_dump(FRuntime *r) {
  if (probe_dumped) return;
  probe_dumped = 1;
  fprintf(stderr, "DEPTH_PROBE steps=%zu depth=%zu peak_depth=%zu binds=%zu pures=%zu reads=%zu last_read_steps=%zu\n",
    r->steps, r->depth, probe_peak_depth, probe_binds, probe_pures, probe_reads, probe_last_read_steps);
  for (size_t i = 0; i < r->depth && i < 512;) {
    const char *label = probe_stack[i] ? probe_stack[i] : "<fold>";
    size_t end = i + 1;
    while (end < r->depth && end < 512 && probe_stack[end] && !strcmp(label, probe_stack[end])) end++;
    fprintf(stderr, "DEPTH_ROW %zu..%zu %s\n", i, end - 1, label);
    i = end;
  }
}
static int enter(FRuntime *r) {''')
    text = replace_once(text,
        '    fail(r, r->depth >= LIMIT_DEPTH(r) ? "native evaluation budget exhausted (depth limit)" : "native evaluation budget exhausted (step limit)");',
        '    probe_dump(r); fail(r, r->depth >= LIMIT_DEPTH(r) ? "native evaluation budget exhausted (depth limit)" : "native evaluation budget exhausted (step limit)");')
    text = replace_once(text,
        'static FValue *evaluate(FRuntime *r, FEval code, FEnv *env) {\n  if (!enter(r)) return NULL;',
        'static FValue *evaluate(FRuntime *r, FEval code, FEnv *env) {\n'
        '  if (r->depth < 512) probe_stack[r->depth] = "<evaluate>";\n'
        '  if (!enter(r)) return NULL;')
    text = replace_once(text,
        'FEval base, FEval step, FThunk *input) {\n  if (!enter(r)) return NULL;',
        'FEval base, FEval step, FThunk *input) {\n'
        '  if (r->depth < 512) probe_stack[r->depth] = "<fold>";\n'
        '  if (!enter(r)) return NULL;')
    text = replace_once(text, 'r->steps++; r->depth++; return 1;',
        'r->steps++; r->depth++;\n'
        '  if (r->depth > probe_peak_depth) probe_peak_depth = r->depth;\n'
        '  return 1;')
    source.write_text(text)
    source = directory/'fibril_binary_runtime.c'
    text = source.read_text()
    for old, new in [
        ('if (io->tag == V_BIND) {', 'if (io->tag == V_BIND) { probe_binds++;'),
        ('if (io->tag == V_PURE) result = io->as.io.first;',
         'if (io->tag == V_PURE) { probe_pures++; result = io->as.io.first; }'),
        ('FByteRead read = fibril_bytes_read(session, capacity);',
         'probe_reads++; probe_last_read_steps = r->steps;\n'
         '        FByteRead read = fibril_bytes_read(session, capacity);'),
    ]:
        text = replace_once(text, old, new)
    source.write_text(text)


def trace_generated(text):
    # Preserve every generated evaluator body; add only an observer label.
    pattern = r'(static FValue \*(fibril_expr_\d+)\(FRuntime \*r, FEnv \*e\) \{)([^\n]*)(\})'
    matches = list(re.finditer(pattern, text))
    if not matches:
        raise ValueError('generated evaluator seam changed')
    def traced(match):
        label = match[2] + ' ' + ' '.join(match[3].split())
        return match[1] + '  header_probe_expression(r, ' + json.dumps(label) + ');\n' + match[3] + match[4]
    text = re.sub(pattern, traced, text)
    return text.replace('#include "fibril_runtime.h"',
        '#include "fibril_runtime.h"\nvoid header_probe_expression(FRuntime *, const char *);', 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fibril', type=Path, required=True)
    parser.add_argument('--fixture', choices=['flat32', 'nested32x32', 'flat1024', 'drain1024', 'drain1024-constant'], default='nested32x32')
    parser.add_argument('--size', type=int, default=14)
    parser.add_argument('--timeout', type=int, default=30)
    args = parser.parse_args()
    if not 1 <= args.size <= 1025 or not 1 <= args.timeout <= 120:
        parser.error('size must be 1..1025; timeout must be 1..120')
    executable = str(args.fibril.resolve())
    root = FIXTURES/args.fixture
    with tempfile.TemporaryDirectory(prefix='fibril-header-depth-') as temporary:
        work = Path(temporary)
        for source in (ROOT/'runtime/native').iterdir():
            if source.is_file():
                shutil.copyfile(source, work/source.name)
        instrument(work)
        emit = [executable, 'emit-c-binary', '--source-dir', str(root), str(root/'Main.fib')]
        result = invoke(emit, timeout=args.timeout)
        if report(args.fixture, 'emit', emit, result) or result[0] != 0:
            return 1
        (work/'main.c').write_text(trace_generated(result[1].decode()))
        (work/'metrics.c').write_text(replace_once(METRICS,
            '  fprintf(stderr,"HEADER_LOOP_METRICS',
            '  probe_dump(&runtime);\n  fprintf(stderr,"HEADER_LOOP_METRICS'))
        command = shlex.split(os.environ.get('CC', 'cc')) + ['-std=c11', '-Wall', '-Wextra', '-Werror', '-I', str(work), str(work/'main.c'), str(work/'metrics.c'), '-o', str(work/'loop')]
        result = invoke(command, timeout=90)
        if report(args.fixture, 'cc-observer', command, result) or result[0] != 0:
            return 1
        command = [str(work/'loop')]
        data = b'a'*(args.size-1) + b':'
        result = invoke(command, data, timeout=args.timeout, open_stdin=True)
        return int(report(args.fixture, 'native-depth-observer', command, result,
            expected=b'' if args.fixture.startswith('drain1024') else data[:-1],
            input_bytes=args.size, stdin_kept_open=True))


if __name__ == '__main__':
    raise SystemExit(main())
