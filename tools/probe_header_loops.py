#!/usr/bin/env python3
"""Non-gating process observations of abandoned header-loop prototypes.

The .fib fixtures perform all byte classification/looping. This client does not
parse headers. Rejections are recorded, not asserted as permanent requirements.
Timeouts remain distinct failures and cause a nonzero probe exit status.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tools/fixtures/header-loop'
METRICS = r'''
#define fibril_native_binary_run uninstrumented_binary_run
#include "fibril_binary_runtime.c"
#undef fibril_native_binary_run
int fibril_native_binary_run(FEval entry,size_t requests,size_t capacity) {
  FRuntime runtime={0};
  FBinaryContext context={&runtime,entry,FB_OK,0,0};
  FByteStatus status=fibril_bytes_run(requests,capacity,stdin,stdout,binary_body,&context);
  fprintf(stderr,"HEADER_LOOP_METRICS %zu %zu %zu %zu\n",
    runtime.steps,runtime.bytes,F_MAX_STEPS,F_MAX_DEPTH);
  return binary_finish(&runtime,&context,status);
}
'''


def invoke(command, data=b'', *, timeout, open_stdin=False):
    start = time.monotonic()
    expired = False
    # File-backed outputs also let open-input probes wait without pipe deadlock.
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.PIPE,
            stdout=stdout, stderr=stderr, start_new_session=True)
        try:
            try:
                if open_stdin:
                    try:
                        process.stdin.write(data)
                        process.stdin.flush()
                    except BrokenPipeError:
                        pass
                    process.wait(timeout=timeout)
                else:
                    process.communicate(data, timeout=timeout)
            except subprocess.TimeoutExpired:
                expired = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            if not process.stdin.closed:
                try:
                    process.stdin.close()
                except BrokenPipeError:
                    pass
        stdout.seek(0)
        stderr.seek(0)
        return process.returncode, stdout.read(), stderr.read(), expired, time.monotonic()-start


def report(fixture, phase, command, result, expected=None, **extra):
    status, out, err, expired, seconds = result
    diagnostic = err.decode('utf-8', errors='replace')
    if expired:
        outcome = 'timeout'
    elif status == 0:
        outcome = 'accepted' if expected is None or out == expected else 'wrong-output'
    elif b'budget exhausted' in err:
        outcome = 'budget-rejection'
    elif b'Binary program rejected input' in err:
        outcome = 'input-rejection'
    else:
        outcome = 'error'
    record = dict(fixture=fixture, phase=phase, command=command, status=status,
        outcome=outcome, seconds=round(seconds, 3), stdout_bytes=len(out),
        stdout_sha256=hashlib.sha256(out).hexdigest(), diagnostic=diagnostic, **extra)
    for line in diagnostic.splitlines():
        if line.startswith('HEADER_LOOP_METRICS '):
            steps, payload, step_limit, depth_limit = map(int, line.split()[1:])
            record.update(native_steps=steps, native_arena_payload=payload,
                native_step_limit=step_limit, native_pure_depth_limit=depth_limit)
            if 'native evaluation budget exhausted' in diagnostic:
                record['native_limit'] = 'steps' if steps >= step_limit else 'depth'
    print(json.dumps(record), flush=True)
    return expired or outcome in ('error', 'wrong-output')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fibril', type=Path, default=ROOT/'build/exec/fibril')
    parser.add_argument('--fixtures', default='flat32,nested32x32,flat1024')
    parser.add_argument('--sizes', default='14,31,32,33,1023,1024,1025')
    parser.add_argument('--timeout', type=int, default=30)
    parser.add_argument('--front-end', action='store_true')
    args = parser.parse_args()
    fixtures = args.fixtures.split(',')
    sizes = [int(n) for n in args.sizes.split(',')]
    if not 1 <= args.timeout <= 120 or len(sizes) > 16 or any(not 1 <= n <= 1025 for n in sizes):
        parser.error('timeout must be 1..120; at most 16 sizes in 1..1025')
    if any(name not in ('flat32', 'nested32x32', 'flat1024') for name in fixtures):
        parser.error('unknown loop fixture')
    executable = str(args.fibril.resolve())
    failed = False
    with tempfile.TemporaryDirectory(prefix='fibril-header-probe-') as temporary:
        work = Path(temporary)
        observer = work/'metrics.c'
        observer.write_text(METRICS)
        for name in fixtures + (['usage-failure', 'expansion-failure'] if args.front_end else []):
            root = FIXTURES/name
            source_args = ['--source-dir', str(root), str(root/'Main.fib')]
            check = [executable, 'check', *source_args]
            result = invoke(check, timeout=args.timeout)
            # Front-end failures are historical observations, not gating tests.
            if name in ('usage-failure', 'expansion-failure'):
                report(name, 'check-only', check, result)
                failed |= result[3]
                continue
            failed |= report(name, 'check', check, result)
            if result[0] != 0:
                continue
            emit = [executable, 'emit-c-binary', *source_args]
            result = invoke(emit, timeout=args.timeout)
            failed |= report(name, 'emit', emit, result)
            native = None
            if result[0] == 0:
                c_source = work/(name+'.c')
                c_source.write_bytes(result[1])
                native_path = work/name
                compile_command = shlex.split(os.environ.get('CC', 'cc')) + [
                    '-std=c11', '-Wall', '-Wextra', '-Werror', '-I', str(ROOT/'runtime/native'),
                    str(c_source), str(observer), '-o', str(native_path)]
                built = invoke(compile_command, timeout=90)
                failed |= report(name, 'cc', compile_command, built)
                if built[0] == 0:
                    native = [str(native_path)]
            commands = [('hosted', [executable, 'run-binary', *source_args])]
            if native:
                commands.append(('native', native))
            for n in sizes:
                data = b'a'*(n-1)+b':'
                for backend, command in commands:
                    result = invoke(command, data, timeout=args.timeout, open_stdin=True)
                    failed |= report(name, backend, command, result, expected=data[:-1],
                        input_bytes=n, stdin_kept_open=True)
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
