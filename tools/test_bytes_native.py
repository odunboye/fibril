#!/usr/bin/env python3
"""Pure Bytes native ABI checks plus actual checked .fib emission/execution.

The C fixture inspects private runtime state deliberately; it is not evidence
of source checking. Source tests independently invoke the built compiler.
"""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

from test_cli import run_cli

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / 'runtime/native'
RAW = r'''
#include "fibril_runtime.c"
#include <assert.h>
static FValue *left_value, *right_value;
static FValue *left(FRuntime *r, FEnv *e) { (void)r; (void)e; return left_value; }
static FValue *right(FRuntime *r, FEnv *e) { (void)r; (void)e; return right_value; }
static FValue *bad_write(FRuntime *r, FEnv *e) { return f_write(r,e,left); }
static void release(FRuntime *r) {
  while(r->allocations) { FAllocation *next=r->allocations->next; free(r->allocations); r->allocations=next; }
}
static FValue *number(FRuntime *r, size_t n) {
  FValue *v=f_nat_zero(r);
  for(size_t i=0;v && i<n;i++) {
    FThunk *tail=ready(r,v);
    v=tail?new_value(r,V_NAT_SUCC):NULL;
    if(v) v->as.recursive.tail=tail;
  }
  return v;
}
int main(int argc, char **argv) {
  if(argc!=2) return 2;
  FRuntime r={0};
  int mode=atoi(argv[1]);
  static unsigned char octets[256];
  for(size_t i=0;i<256;i++) octets[i]=(unsigned char)i;
  if(mode==0) {
    left_value=f_bytes_literal(&r,octets,256);
    right_value=f_bytes_literal(&r,NULL,0);
    FValue *copy=f_bytes_append(&r,NULL,left,right);
    assert(copy && copy->tag==V_BYTES && copy->as.bytes.length==256);
    assert(!memcmp(copy->as.bytes.data,octets,256));
    left_value=copy;
    FValue *n=f_bytes_length(&r,NULL,left);
    size_t count=0;
    while(n && n->tag==V_NAT_SUCC) { count++; n=force(&r,n->as.recursive.tail); }
    assert(n && n->tag==V_NAT_ZERO && count==256 && !r.error);
  } else if(mode==1) {
    for(size_t n=0;n<=513;n++) {
      left_value=number(&r,n);
      FValue *value=f_bytes_octet(&r,NULL,left);
      assert(value && value->tag==V_BYTES && value->as.bytes.length==1);
      assert(value->as.bytes.data[0]==(unsigned char)n && !r.error);
      release(&r); memset(&r,0,sizeof(r));
    }
    assert(!r.error);
  } else if(mode==2) {
    left_value=f_literal(&r,octets,256);
    assert(!f_bytes_length(&r,NULL,left) && r.error);
  } else if(mode==3) {
    left_value=f_bytes_literal(&r,octets,256);
    right_value=left_value;
    assert(!f_append(&r,NULL,left,right) && r.error);
  } else if(mode==4) {
    assert(!f_bytes_literal(&r,NULL,1) && r.error);
  } else if(mode==5) {
    left_value=f_bytes_literal(&r,octets,256);
    right_value=left_value;
    r.bytes=F_MAX_BYTES;
    assert(!f_bytes_append(&r,NULL,left,right) && r.error);
  } else if(mode==6) {
    left_value=f_bytes_literal(&r,octets,256);
    r.steps=F_MAX_STEPS-10;
    assert(!f_bytes_length(&r,NULL,left) && r.error);
  } else if(mode==7) {
    left_value=number(&r,1);
    left_value->as.recursive.tail->value=left_value;
    r.steps=F_MAX_STEPS-10;
    assert(!f_bytes_octet(&r,NULL,left) && r.error);
  } else if(mode==8) {
    left_value=f_nat_zero(&r);
    assert(f_bytes_octet(&r,NULL,left)); /* Zero is a legitimate octet. */
    left_value=f_unit(&r);
    assert(!f_bytes_octet(&r,NULL,left) && r.error);
  } else if(mode==9) {
    FValue fake={0}; fake.tag=V_BYTES; fake.as.bytes.length=SIZE_MAX;
    left_value=&fake; right_value=f_bytes_literal(&r,octets,1);
    assert(!f_bytes_append(&r,NULL,left,right) && r.error);
  } else if(mode==10) {
    left_value=f_bytes_literal(&r,octets,1); right_value=f_literal(&r,octets,1);
    assert(!f_bytes_append(&r,NULL,left,right) && r.error);
  } else if(mode==11) {
    assert(!f_bytes_length(&r,NULL,NULL) && r.error);
    r.error=NULL;
    assert(!f_bytes_octet(&r,NULL,NULL) && r.error);
    r.error=NULL;
    assert(!f_bytes_append(&r,NULL,left,NULL) && r.error);
  } else if(mode==12) {
    assert(!f_bytes_literal(&r,octets,SIZE_MAX) && r.error);
  } else if(mode==13) {
    left_value=f_bytes_literal(&r,octets,256);
    int status=fibril_native_run(bad_write);
    release(&r); return status;
  } else return 2;
  release(&r);
  return 0;
}
'''


class NativeBytes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='fibril-pure-bytes-')
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.work = Path(cls.temporary.name)
        cls.cc = shlex.split(os.environ.get('CC', 'cc'))
        source = cls.work / 'raw.c'
        source.write_text(RAW)
        cls.raw = cls.work / 'raw'
        compiled = subprocess.run(cls.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror',
            '-I', str(RUNTIME), str(source), '-o', str(cls.raw)], capture_output=True, timeout=60)
        if compiled.returncode:
            raise AssertionError(compiled.stderr.decode(errors='replace'))

    def test_raw_native_byte_facts(self):
        for mode in range(13):
            with self.subTest(mode=mode):
                result = subprocess.run([str(self.raw), str(mode)], capture_output=True, timeout=20)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'', b''))

    def test_native_byte_value_is_not_text_output(self):
        result = subprocess.run([str(self.raw), '13'], capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, b'')
        self.assertIn(b'write expects a string', result.stderr)

    def test_checked_source_uses_byte_lowering_in_both_modes(self):
        example = 'examples/core/bytes-native.fib'
        for command in ('run', 'run-interactive'):
            result = run_cli(command, example)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (0, 'xx\n', ''))
        for command in ('emit-c', 'emit-c-interactive'):
            with self.subTest(command=command):
                emitted = run_cli(command, example)
                self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
                for function in ('f_bytes_literal', 'f_bytes_append', 'f_bytes_length', 'f_bytes_octet'):
                    self.assertIn(function + '(', emitted.stdout)
                source = self.work / (command + '.c')
                source.write_text(emitted.stdout)
                executable = self.work / command
                compiled = subprocess.run(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror',
                    '-I', str(RUNTIME), str(source), str(RUNTIME / 'fibril_runtime.c'), '-o', str(executable)],
                    capture_output=True, timeout=60)
                self.assertEqual(compiled.returncode, 0, compiled.stderr.decode(errors='replace'))
                result = subprocess.run([str(executable)], capture_output=True, timeout=20)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'xx\n', b''))


if __name__ == '__main__':
    unittest.main()
