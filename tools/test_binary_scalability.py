#!/usr/bin/env python3
"""Native binary IO-stack scalability, bounds and failure semantics.

Raw C fixtures are not source checking. A separate test compiles a real .fib
workload without changing compiler/evaluator/transport limits.
"""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

from test_cli import run_cli

ROOT=Path(__file__).resolve().parents[1]
RUNTIME=ROOT/'runtime/native'
RAW=r'''
#include "fibril_binary_runtime.c"
#include <assert.h>
static FValue *program;
static size_t flushes,remaining,fail_at;
static int failure_mode;
static FRuntime *active_runtime;
static int read_host(void *c) { (void)c;return -1; }
static int write_host(void *c,unsigned char b) { (void)c;(void)b;return 0; }
static int flush_host_test(void *c) {
  (void)c;flushes++;
  if(flushes==3 && failure_mode==6) active_runtime->steps=F_MAX_STEPS;
  if(flushes==3 && failure_mode==7) active_runtime->bytes=F_MAX_BYTES;
  return fail_at && flushes==fail_at?-1:0;
}
static FValue *unit(FRuntime *r,FEnv *e) { (void)e;return f_unit(r); }
static FValue *pure(FRuntime *r,FEnv *e) { return f_pure(r,e,unit); }
static FValue *flush(FRuntime *r,FEnv *e) { (void)e;return f_flush_bytes(r); }
static FValue *consume(FRuntime *r,FEnv *e) { return f_variable(r,e,0); }
static FValue *after(FRuntime *r,FEnv *e) { return f_unit_case(r,e,consume,flush); }
static FValue *entry(FRuntime *r,FEnv *e) { (void)r;(void)e;return program; }
static FValue *tail_entry(FRuntime *r,FEnv *e);
static FValue *tail_body(FRuntime *r,FEnv *e) { return f_unit_case(r,e,consume,tail_entry); }
static FValue *tail_next(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,tail_body); }
static FValue *tail_entry(FRuntime *r,FEnv *e) {
  if(remaining) { remaining--;return f_bind(r,e,flush,tail_next); }
  return pure(r,e);
}
static FValue *bad(FRuntime *r,FEnv *e) { (void)e;fail(r,"lazy value forced");return NULL; }
static FValue *lazy_entry(FRuntime *r,FEnv *e) {
  FValue *first=f_pure(r,e,bad),*next=f_lambda(r,e,1,flush);
  FValue *io=first && next?new_value(r,V_BIND):NULL;
  if(io) { io->as.io.first=ready(r,first);io->as.io.second=ready(r,next); }
  return io;
}
int main(int argc,char **argv) {
  if(argc!=3) return 2;
  int mode=atoi(argv[1]);size_t n=(size_t)strtoul(argv[2],NULL,10);
  FRuntime r={0};FEval code=entry;failure_mode=mode;active_runtime=&r;
  if(mode==4) { remaining=n;code=tail_entry; }
  else if(mode==5) code=lazy_entry;
  else {
    program=pure(&r,NULL);
    FValue *next=f_lambda(&r,NULL,0,after);
    FThunk *continuation=ready(&r,next);
    for(size_t i=0;i<n;i++) {
      FThunk *first=ready(&r,program);
      program=new_value(&r,V_BIND);
      assert(first && program && continuation);
      program->as.io.first=first;program->as.io.second=continuation;
    }
  }
  if(mode==1) fail_at=3;
  if(mode==2) r.steps=F_MAX_STEPS-3;
  if(mode==3) r.bytes=F_MAX_BYTES;
  FBinaryContext context={&r,code,FB_OK,0,0};
  FByteStatus status=fibril_bytes_run_with(10000,0,
    (FByteAdapters){read_host,write_host,flush_host_test,NULL},binary_body,&context);
  assert(r.depth==0);
  if(mode==0 && n<=F_MAX_BINARY_PENDING) assert(status==FB_OK && !r.error && flushes==n+1);
  else if(mode==0) assert(status==FB_ADAPTER_VIOLATION && r.error && strstr(r.error,"continuation budget") && !flushes);
  else if(mode==1) assert(status==FB_FLUSH_FAILED && !r.error && flushes==3);
  else if(mode==2) assert(status==FB_ADAPTER_VIOLATION && r.error && strstr(r.error,"evaluation budget") && !flushes);
  else if(mode==3) assert(status==FB_ADAPTER_VIOLATION && r.error && strstr(r.error,"allocation budget") && !flushes);
  else if(mode==4) {
    assert(status==FB_OK && !r.error && flushes==n+1);
    /* Private fixture accounting: one reusable control node, not n nodes. */
    size_t expected=n*(4*sizeof(FValue)+3*sizeof(FThunk)+sizeof(FEnv))+
                    2*sizeof(FValue)+sizeof(FThunk)+(n?sizeof(FBinaryPending):0);
    assert(r.bytes==expected);
  }
  else if(mode==5) assert(status==FB_OK && !r.error && flushes==2);
  else if(mode==6) assert(status==FB_ADAPTER_VIOLATION && r.error && strstr(r.error,"evaluation budget") && flushes==3);
  else if(mode==7) assert(status==FB_ADAPTER_VIOLATION && r.error && strstr(r.error,"allocation budget") && flushes==3);
  else return 2;
  while(r.allocations) { FAllocation *next=r.allocations->next;free(r.allocations);r.allocations=next; }
  return 0;
}
'''


class BinaryScalability(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory(prefix='fibril-bind-stack-')
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.work=Path(cls.temporary.name)
        cls.cc=shlex.split(os.environ.get('CC','cc'))
        source=cls.work/'raw.c';source.write_text(RAW)
        cls.raw=cls.work/'raw'
        built=subprocess.run(cls.cc+['-std=c11','-Wall','-Wextra','-Werror','-I',str(RUNTIME),
            str(source),'-o',str(cls.raw)],capture_output=True,timeout=90)
        if built.returncode:raise AssertionError(built.stderr)

    def check_raw(self,mode,n):
        result=subprocess.run([str(self.raw),str(mode),str(n)],capture_output=True,timeout=30)
        self.assertEqual((result.returncode,result.stdout,result.stderr),(0,b'',b''))

    def test_pending_depth_boundaries(self):
        for n in (0,1,511,512,1024,4096,4097):
            with self.subTest(n=n):self.check_raw(0,n)

    def test_transport_failure_skips_continuations_and_final_flush(self):
        self.check_raw(1,1024)

    def test_step_exhaustion_while_pushing(self):
        self.check_raw(2,1024)

    def test_allocation_exhaustion_while_pushing(self):
        self.check_raw(3,16)

    def test_step_exhaustion_after_effects(self):
        self.check_raw(6,1024)

    def test_allocation_exhaustion_after_effects(self):
        self.check_raw(7,1024)

    def test_tail_sequence_reuses_popped_frames(self):
        self.check_raw(4,4096)

    def test_pure_result_remains_lazy_for_erased_continuation(self):
        self.check_raw(5,0)

    def test_checked_native_512_bind_workload(self):
        emitted=run_cli('emit-c-binary','examples/core/binary-many-binds.fib')
        self.assertEqual(emitted.returncode,0,emitted.stdout+emitted.stderr)
        source=self.work/'many.c';source.write_text(emitted.stdout)
        executable=self.work/'many'
        built=subprocess.run(self.cc+['-std=c11','-Wall','-Wextra','-Werror','-I',str(RUNTIME),
            str(source),str(RUNTIME/'fibril_binary_runtime.c'),'-o',str(executable)],capture_output=True,timeout=90)
        self.assertEqual(built.returncode,0,built.stderr)
        result=subprocess.run([str(executable)],capture_output=True,timeout=30)
        self.assertEqual((result.returncode,result.stdout,result.stderr),(0,b'',b''))


if __name__=='__main__':unittest.main()
