#!/usr/bin/env python3
"""Bounded source-level probes for numeric work on the path to larger frames.

Reports observations, never timing assertions. Does not change runner budgets or
implement framing. Probe payloads are opaque bytes; stdout must match exactly.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]
EXE=ROOT/'build/exec/fibril'
RUNTIME=ROOT/'runtime/native'

# Observe private runtime counters after the real session. No parser or numeric
# operation is implemented here, and no runtime limit is changed.
PROFILE=r'''
#define fibril_native_binary_run unprofiled_binary_run
#include "fibril_binary_runtime.c"
#undef fibril_native_binary_run
int fibril_native_binary_run(FEval entry,size_t requests,size_t capacity) {
  FRuntime runtime={0};
  FBinaryContext context={&runtime,entry,FB_OK,0,0};
  FByteStatus status=fibril_bytes_run(requests,capacity,stdin,stdout,binary_body,&context);
  fprintf(stderr,"FIBRIL_NUMERIC_METRICS %zu %zu %zu %zu\n",runtime.steps,runtime.bytes,F_MAX_STEPS,F_MAX_DEPTH);
  return binary_finish(&runtime,&context,status);
}
'''


def native_observation(result,expected):
    prefix=b'FIBRIL_NUMERIC_METRICS '
    lines=result['stderr'].splitlines(keepends=True)
    metrics=[line for line in lines if line.startswith(prefix)]
    if len(metrics)!=1:return classify(result,expected)
    fields=metrics[0][len(prefix):].split()
    if len(fields)!=4 or not all(field.isdigit() for field in fields):return classify(result,expected)
    clean=dict(result);clean['stderr']=b''.join(line for line in lines if line!=metrics[0])
    observation=classify(clean,expected)
    observation['evaluator_steps']=int(fields[0]);observation['arena_payload_bytes']=int(fields[1])
    observation['step_limit']=int(fields[2]);observation['pure_depth_limit']=int(fields[3])
    if 'native evaluation budget exhausted' in observation['diagnostic']:
        observation['native_limit']='steps' if int(fields[0])>=int(fields[2]) else 'depth'
    return observation


def invoke(command,data=b'',timeout=30):
    start=time.perf_counter()
    process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,start_new_session=True)
    expired=False
    try:
        try:out,err=process.communicate(data,timeout=timeout)
        except subprocess.TimeoutExpired:
            expired=True;os.killpg(process.pid,signal.SIGKILL)
            out,err=process.communicate()
        return {'status':process.returncode,'timeout':expired,
            'seconds':time.perf_counter()-start,'stdout':out,'stderr':err}
    finally:
        if process.poll() is None:os.killpg(process.pid,signal.SIGKILL);process.wait()
        for stream in (process.stdin,process.stdout,process.stderr):stream.close()


def natural(n):
    value='Zero'
    for _ in range(n):value='(Succ '+value+')'
    return value


def program(n,method,checked):
    if not 1<=n<=4096:raise ValueError('probe size must be 1..4096')
    if method=='byte-count':
        count='primUTF8Case Bytes Nat (primUTF8Encode "'+('x'*n)+'") Zero (\\(1 b : Bytes) => primBytesLength b)'
        helpers=''
    elif method in ('decimal','decimal-fold'):
        # Same mathematical accumulation, two structurally different Nat folds.
        helpers=('add : (1 a : Nat) -> (1 b : Nat) -> Nat\n'
            'add = \\(1 a : Nat) => \\(1 b : Nat) => natRec (\\(0 n : Nat) => Nat) b (\\(0 n : Nat) => \\(1 old : Nat) => Succ old) a\n'
            'ten : Nat\nten = '+natural(10)+'\n'
            'tens : (value : Nat) -> Nat\n')
        if method=='decimal':
            helpers+='tens = \\(value : Nat) => natRec (\\(0 n : Nat) => Nat) Zero (\\(0 n : Nat) => \\(1 old : Nat) => add value old) ten\n'
        else:
            helpers+='tens = \\(value : Nat) => natRec (\\(0 n : Nat) => Nat) Zero (\\(0 n : Nat) => \\(1 old : Nat) => add ten old) value\n'
        count=natural(int(str(n)[0]))
        for digit in str(n)[1:]:count='add (tens ('+count+')) '+natural(int(digit))
    elif method=='byte-decimal':
        helpers=('digitBytes : (value : Nat) -> Bytes\n'
            'digitBytes = \\(value : Nat) => natRec (\\(0 n : Nat) => Bytes) primBytesEmpty (\\(0 n : Nat) => \\(1 old : Bytes) => primBytesAppend old (primBytesOctetMod256 Zero)) value\n'
            'tenBytes : (value : Bytes) -> Bytes\n'
            'tenBytes = \\(value : Bytes) => let (twice : Bytes) = primBytesAppend value value in let (four : Bytes) = primBytesAppend twice twice in let (eight : Bytes) = primBytesAppend four four in primBytesAppend eight twice\n')
        stages=[]
        for i,digit in enumerate(str(n)):
            expression='digitBytes '+natural(int(digit))
            if i:expression='primBytesAppend (tenBytes value'+str(i-1)+') ('+expression+')'
            stages.append('case primBytesShare ('+expression+') of Shared value'+str(i)+' => ')
        count=''.join(stages)+'primBytesLength value'+str(len(stages)-1)
    else:raise ValueError('unknown count construction')
    # Keep the count as a lexical binding; global closed-term substitution is a
    # separate source-scaling factor. Checked mode also reuses it after reading.
    chunk=('if primBytesLengthIs count value then send value else primRejectBytes'
        if checked else 'send value')
    return 'module Probe\n\n'+helpers+('record SharedBytes : Type where\n  constructor Shared\n  bytes : Bytes\n'
        'main : IO Unit\nmain =\n  let (count : Nat) = '+count+' in\n'
        '  let (send : (1 bytes : Bytes) -> IO Unit) = \\(1 bytes : Bytes) => bind Unit Unit (primWriteBytes bytes) (\\(1 done : Unit) => case done of () => primFlushBytes) in\n'
        '  bind ByteReadResult Unit (primReadBytes count) (\\(1 result : ByteReadResult) => primByteReadCase (IO Unit) result primRejectBytes (\\(1 bytes : Bytes) => case primBytesShare bytes of Shared value => '+chunk+'))\n')


def classify(result,expected):
    err=result['stderr'].decode(errors='replace')
    if result['timeout']:outcome='timeout'
    elif result['status']==0 and result['stdout']==expected and not err:outcome='ok'
    elif result['status']==0:outcome='incorrect-output'
    elif result['status']<0:outcome='signal'
    elif any(marker in err for marker in ('AddressSanitizer','UndefinedBehaviorSanitizer','runtime error:')):outcome='error'
    elif 'budget' in err.lower() or 'admission' in err.lower() or 'exceed' in err.lower():outcome='bounded-rejection'
    else:outcome='error'
    return {'outcome':outcome,'status':result['status'],'seconds':result['seconds'],
        'output_bytes':len(result['stdout']),'diagnostic':err[:4096]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sizes',default='99,256,512,1024,4096')
    parser.add_argument('--methods',default='decimal,decimal-fold,byte-count,byte-decimal')
    parser.add_argument('--timeout',type=int,default=30)
    parser.add_argument('--host-only',action='store_true')
    args=parser.parse_args()
    try:sizes=[int(n) for n in args.sizes.split(',')]
    except ValueError:parser.error('sizes must be comma-separated integers')
    methods=args.methods.split(',')
    if not sizes or len(sizes)>8 or any(n<1 or n>4096 for n in sizes):parser.error('1..8 sizes, each 1..4096')
    if not methods or len(methods)>4 or any(m not in ('decimal','decimal-fold','byte-count','byte-decimal') for m in methods):parser.error('unknown methods')
    if not 1<=args.timeout<=120:parser.error('timeout must be 1..120 seconds')
    observations=[]
    with tempfile.TemporaryDirectory(prefix='fibril-number-probes-') as tmp:
        work=Path(tmp)
        observer=work/'observer.c';observer.write_text(PROFILE)
        for n in sizes:
            data=bytes(i%256 for i in range(n))
            for method in methods:
                for checked in (False,True):
                    source=work/'Probe.fib';source.write_text(program(n,method,checked))
                    item={'kind':'unframed-numeric-probe','runner_limits_changed':False,
                        'bytes':n,'method':method,'checked_length':checked}
                    item['hosted']=classify(invoke([str(EXE),'run-binary','--source-dir',str(work),str(source)],data,args.timeout),data)
                    if not args.host_only:
                        emitted=invoke([str(EXE),'emit-c-binary','--source-dir',str(work),str(source)],timeout=args.timeout)
                        if emitted['status'] or emitted['timeout']:
                            item['emission']=classify(emitted,b'')
                        else:
                            c=work/'probe.c';c.write_bytes(emitted['stdout']);executable=work/'probe'
                            built=invoke(shlex.split(os.environ.get('CC','cc'))+['-std=c11','-O2','-Wall','-Wextra','-Werror','-I',str(RUNTIME),str(c),str(observer),'-o',str(executable)],timeout=args.timeout)
                            if built['status'] or built['timeout']:item['compilation']=classify(built,b'')
                            else:item['native']=native_observation(invoke([str(executable)],data,args.timeout),data)
                    observations.append(item)
                    print(json.dumps(item),flush=True)
    # Unexpected outcomes are failures, not successful bounded-limit evidence.
    bad=any(result['outcome'] not in ('ok','bounded-rejection') or
        (key=='compilation' and result['outcome']!='ok')
        for item in observations for key,result in item.items() if key in ('hosted','native','emission','compilation'))
    return 1 if bad else 0


if __name__=='__main__':raise SystemExit(main())
