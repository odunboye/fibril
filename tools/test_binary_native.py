#!/usr/bin/env python3
"""Trusted native binary bridge fault tests, separate from source checking."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / 'runtime/native'
HARNESS = r'''
#include "fibril_binary_runtime.c"
#include <assert.h>
typedef struct { size_t reads,writes,flushes,length; int mode; FRuntime *runtime; } Host;
static const unsigned char payload[]={0,255,13,10};
static int read_host(void *opaque) {
  Host *h=opaque;
  if(h->mode==4 && h->reads==2) return -2;
  if(h->reads==h->length) return -1;
  return payload[h->reads++];
}
static int write_host(void *opaque,unsigned char byte) {
  Host *h=opaque;
  if(h->mode==5 && h->writes==1) return -1;
  assert(h->writes<sizeof(payload) && byte==payload[h->writes]); h->writes++;return 0;
}
static int bridge_flush(void *opaque) { Host *h=opaque;h->flushes++;return h->mode==6?-1:0; }
static FValue *data(FRuntime *r,FEnv *e) { (void)e;return f_bytes_literal(r,payload,sizeof(payload)); }
static FValue *unit(FRuntime *r,FEnv *e) { (void)e;return f_unit(r); }
static FValue *pure(FRuntime *r,FEnv *e) { return f_pure(r,e,unit); }
static FValue *capacity(FRuntime *r,FEnv *e) { return f_bytes_length(r,e,data); }
static FValue *capacity_fail(FRuntime *r,FEnv *e) {
  FValue *n=capacity(r,e);r->bytes=F_MAX_BYTES;return n;
}
static FValue *read_normal(FRuntime *r,FEnv *e) { return f_read_bytes(r,e,capacity); }
static FValue *read_alloc_fail(FRuntime *r,FEnv *e) { return f_read_bytes(r,e,capacity_fail); }
static FValue *consume(FRuntime *r,FEnv *e) { return f_variable(r,e,0); }
static FValue *write_payload(FRuntime *r,FEnv *e) { return f_write_bytes(r,e,consume); }
static FValue *chunk(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,write_payload); }
static FValue *choose(FRuntime *r,FEnv *e) {
  FEval branches[]={pure,chunk};return f_variant_case(r,e,consume,2,branches);
}
static FValue *next(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,choose); }
static FValue *echo(FRuntime *r,FEnv *e) { return f_bind(r,e,read_normal,next); }
static FValue *echo_alloc_fail(FRuntime *r,FEnv *e) { return f_bind(r,e,read_alloc_fail,next); }
static FValue *flush(FRuntime *r,FEnv *e) { (void)e;return f_flush_bytes(r); }
static FValue *zero(FRuntime *r,FEnv *e) { (void)e;return f_nat_zero(r); }
static FValue *read_zero(FRuntime *r,FEnv *e) { return f_read_bytes(r,e,zero); }
static FValue *bad_main(FRuntime *r,FEnv *e) { return f_pure(r,e,data); }
static FValue *write_direct(FRuntime *r,FEnv *e) { return f_write_bytes(r,e,data); }
static FValue *bad_next(FRuntime *r,FEnv *e) { return f_lambda(r,e,0,unit); }
static FValue *bad_later(FRuntime *r,FEnv *e) { return f_bind(r,e,write_direct,bad_next); }
int main(int argc,char **argv) {
  if(argc!=2) return 2;
  int mode=atoi(argv[1]);FRuntime r={0};Host h={0,0,0,4,mode,&r};
  size_t requests=2,bytes=8;FEval entry=echo;
  if(mode==1 || mode==2) { h.length=2;bytes=mode==1?6:5; }
  if(mode==3) { h.length=0;requests=1;bytes=4; }
  if(mode==6) { entry=pure;requests=0;bytes=0; }
  if(mode==7) { entry=flush;requests=1;bytes=0; }
  if(mode==8) { entry=read_zero;requests=1;bytes=0; }
  if(mode==9) { entry=bad_main;requests=0;bytes=0; }
  if(mode==10) entry=echo_alloc_fail;
  if(mode==11) entry=bad_later;
  if(mode==12) requests=100001;
  FBinaryContext context={&r,entry,FB_OK,0,0};
  FByteStatus status=fibril_bytes_run_with(requests,bytes,
      (FByteAdapters){read_host,write_host,bridge_flush,&h},binary_body,&context);
  if(mode==0) assert(status==FB_OK && h.writes==4 && h.flushes==1);
  else if(mode==1) assert(status==FB_OK && h.writes==2 && h.flushes==1);
  else if(mode==2) assert(status==FB_BYTE_LIMIT && h.reads==2 && !h.writes && !h.flushes);
  else if(mode==3) assert(status==FB_OK && !h.writes && h.flushes==1);
  else if(mode==4) assert(status==FB_READ_FAILED && context.read_prefix==2 && !h.writes && !h.flushes);
  else if(mode==5) assert(status==FB_WRITE_FAILED && context.write_prefix==1 && h.writes==1 && !h.flushes);
  else if(mode==6) assert(status==FB_FLUSH_FAILED && h.flushes==1);
  else if(mode==7) assert(status==FB_OK && h.flushes==2);
  else if(mode==8) assert(status==FB_ZERO_READ && !h.reads && !h.flushes);
  else if(mode==9) assert(status==FB_ADAPTER_VIOLATION && r.error && !h.flushes);
  else if(mode==10) assert(status==FB_ADAPTER_VIOLATION && r.error && h.reads==4 && !h.flushes);
  else if(mode==11) assert(status==FB_ADAPTER_VIOLATION && r.error && h.writes==4 && !h.flushes);
  else if(mode==12) {
    assert(status==FB_ADMISSION && !r.steps && !r.allocations && !h.flushes);
    assert(!f_read_bytes(&r,NULL,NULL) && r.error);r.error=NULL;
    assert(!f_write_bytes(&r,NULL,NULL) && r.error);
  }
  else return 2;
  while(r.allocations) { FAllocation *next=r.allocations->next;free(r.allocations);r.allocations=next; }
  return 0;
}
'''


class NativeBinaryBridge(unittest.TestCase):
    def test_represented_returns_cleanup_and_accounting(self):
        with tempfile.TemporaryDirectory(prefix='fibril-binary-bridge-') as directory:
            source=Path(directory)/'bridge.c'
            executable=Path(directory)/'bridge'
            source.write_text(HARNESS)
            cc=shlex.split(os.environ.get('CC','cc'))
            built=subprocess.run(cc+['-std=c11','-Wall','-Wextra','-Werror','-I',str(RUNTIME),
                str(source),'-o',str(executable)],capture_output=True,timeout=60)
            self.assertEqual(built.returncode,0,built.stderr)
            for mode in range(13):
                with self.subTest(mode=mode):
                    result=subprocess.run([str(executable),str(mode)],capture_output=True,timeout=20)
                    self.assertEqual((result.returncode,result.stdout,result.stderr),(0,b'',b''))


if __name__=='__main__':
    unittest.main()
