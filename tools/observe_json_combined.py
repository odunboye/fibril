#!/usr/bin/env python3
"""Observe the shared diagnostic on hosted and pair-enabled native backends.

Budget blockers are reported, not counted as successful JSON executions.
Requires a built compiler; honors FIBRIL and CC. Does not implement JSON/framing.
"""
import json
import os
from pathlib import Path
import shlex
import tempfile

from bench_binary_numbers import invoke
from observe_json_state_sharing import FIXTURES, ROOT, cases, check_source_preservation, oracle


def category(result,expected,data,native=False):
    status,out,err=result['status'],result['stdout'],result['stderr']
    if result['timeout']:return 'timeout'
    if any(marker in err for marker in (b'AddressSanitizer',b'UndefinedBehaviorSanitizer',b'runtime error:')):
        return 'unexpected_failure'
    if status==0:return 'match' if out==expected and not err else 'mismatch'
    if not data and status==1 and not out and b'Binary program rejected input' in err:
        return 'wrapper_eof'
    if status==1 and not out:
        if not native and err==b'Binary reduction budget exhausted\n':return 'runtime_blocked'
        if native and err.startswith(b'fibril native binary: ') and err.endswith(b'budget exhausted\n'):
            return 'runtime_blocked'
    return 'unexpected_failure'


def main():
    check_source_preservation()
    exe=os.environ.get('FIBRIL',str(ROOT/'build/exec/fibril'))
    source=FIXTURES/'shared'
    arguments=['--source-dir',str(source),str(source/'Read65.fib')]
    totals={backend:{key:0 for key in ('match','runtime_blocked','wrapper_eof','mismatch','unexpected_failure','timeout')}
        for backend in ('hosted','native')}
    with tempfile.TemporaryDirectory(prefix='fibril-json-combined-') as temporary:
        work=Path(temporary)
        emitted=invoke([exe,'emit-c-binary',*arguments],timeout=90)
        if emitted['status'] or emitted['timeout']:
            raise SystemExit('Native emission failed: '+repr(emitted['stderr']))
        c=work/'shared.c';c.write_bytes(emitted['stdout'])
        executable=work/'shared'
        built=invoke(shlex.split(os.environ.get('CC','cc'))+['-std=c11','-O2','-Wall','-Wextra','-Werror',
            '-I',str(ROOT/'runtime/native'),str(c),str(ROOT/'runtime/native/fibril_binary_runtime.c'),'-o',str(executable)],timeout=90)
        if built['status'] or built['timeout']:
            raise SystemExit('Native compilation failed: '+repr(built['stderr']))
        extra=[('duplicate-invalid-first',b'{"a":"\\ud800","a":0}'),
            ('duplicate-invalid-last',b'{"a":0,"a":"\\ud800"}'),
            ('duplicate-invalid-nested',b'{"a":{"x":"\\ud800"},"a":0}')]
        for label,data in [*cases(),*extra]:
            _,_,expected=oracle(data)
            for backend,command in [('hosted',[exe,'run-binary',*arguments]),('native',[str(executable)])]:
                result=invoke(command,data,timeout=30)
                outcome=category(result,expected,data,backend=='native')
                totals[backend][outcome]+=1
                print(json.dumps({'case':label,'backend':backend,'input_hex':data.hex(),
                    'expected_hex':expected.hex(),'status':result['status'],
                    'stdout_hex':result['stdout'].hex(),'stderr':result['stderr'].decode(errors='replace'),
                    'seconds':result['seconds'],'category':outcome}),flush=True)
    print(json.dumps({'summary':totals,'scope':'diagnostic only; not full JSON or 4096-byte validation'}),flush=True)
    return int(any(counts[key] for counts in totals.values()
        for key in ('mismatch','unexpected_failure','timeout')))


if __name__=='__main__':raise SystemExit(main())
