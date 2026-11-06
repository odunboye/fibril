#!/usr/bin/env python3
"""Pure Bytes native ABI checks plus actual checked .fib emission/execution.

The C fixture inspects private runtime state deliberately; it is not evidence
of source checking. Source tests independently invoke the built compiler.
"""
import os
import random
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
static FValue *left_value, *right_value, *third_value;
static FValue *left(FRuntime *r, FEnv *e) { (void)r; (void)e; return left_value; }
static FValue *right(FRuntime *r, FEnv *e) { (void)r; (void)e; return right_value; }
static FValue *third(FRuntime *r, FEnv *e) { (void)r; (void)e; return third_value; }
static size_t read_number(FRuntime *r, FValue *value) {
  size_t n=0;
  while(value && value->tag==V_NAT_SUCC && n<1024) { n++; value=force(r,value->as.recursive.tail); }
  assert(value && value->tag==V_NAT_ZERO); return n;
}
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
  } else if(mode==14) {
    for(size_t n=0;n<258;n++) {
      left_value=number(&r,n); right_value=f_bytes_literal(&r,octets,256);
      FValue *result=f_bytes_index(&r,NULL,left,right);
      assert(result && result->tag==V_VARIANT);
      if(n<256) {
        assert(result->as.variant.tag==1 && result->as.variant.payload);
        assert(read_number(&r,force(&r,result->as.variant.payload))==n);
      } else assert(result->as.variant.tag==0 && !result->as.variant.payload);
      assert(!r.error); release(&r); memset(&r,0,sizeof(r));
    }
  } else if(mode==15) {
    for(size_t start=0;start<8;start++) for(size_t count=0;count<8;count++) {
      left_value=number(&r,start); right_value=number(&r,count);
      third_value=f_bytes_literal(&r,octets,4);
      FValue *view=f_bytes_slice(&r,NULL,left,right,third);
      size_t offset=start>4?4:start, length=count<4-offset?count:4-offset;
      assert(view && view->tag==V_BYTES && view->as.bytes.length==length);
      if(length) assert(!memcmp(view->as.bytes.data,octets+offset,length));
      left_value=view; right_value=f_bytes_literal(&r,octets,256);
      FValue *copy=f_bytes_append(&r,NULL,left,right);
      assert(copy && copy->as.bytes.length==length+256);
      if(length) assert(!memcmp(view->as.bytes.data,copy->as.bytes.data,length));
      assert(!r.error); release(&r); memset(&r,0,sizeof(r));
    }
  } else if(mode==16) {
    left_value=number(&r,0); right_value=f_unit(&r);
    assert(!f_bytes_index(&r,NULL,left,right) && r.error);
    r.error=NULL; third_value=f_bytes_literal(&r,octets,4);
    assert(!f_bytes_slice(&r,NULL,left,right,third) && r.error);
  } else if(mode==17) {
    left_value=number(&r,0); right_value=f_bytes_literal(&r,octets+255,1);
    r.steps=F_MAX_STEPS-2;
    assert(!f_bytes_index(&r,NULL,left,right) && r.error);
  } else if(mode==18) {
    assert(!f_bytes_index(&r,NULL,NULL,right) && r.error);
    r.error=NULL; assert(!f_bytes_slice(&r,NULL,left,right,NULL) && r.error);
  } else if(mode==19) {
    left_value=number(&r,1); left_value->as.recursive.tail->value=left_value;
    right_value=f_bytes_literal(&r,octets,4); r.steps=F_MAX_STEPS-10;
    assert(!f_bytes_index(&r,NULL,left,right) && r.error);
  } else if(mode==20) {
    int length;
    while((length=fgetc(stdin))!=EOF) {
      unsigned char data[64];
      if(length>64 || fread(data,1,(size_t)length,stdin)!=(size_t)length) return 2;
      left_value=f_bytes_literal(&r,data,(size_t)length);
      FValue *decoded=f_utf8_decode(&r,NULL,left);
      assert(decoded && decoded->tag==V_VARIANT && !r.error);
      int valid=decoded->as.variant.tag==1;
      if(valid) {
        left_value=force(&r,decoded->as.variant.payload);
        assert(left_value && left_value->tag==V_STRING && left_value->as.string.length==(size_t)length);
        assert(!memcmp(left_value->as.string.bytes,data,(size_t)length));
        FValue *encoded=f_utf8_encode(&r,NULL,left);
        assert(encoded && encoded->tag==V_VARIANT && encoded->as.variant.tag==1);
        FValue *bytes=force(&r,encoded->as.variant.payload);
        assert(bytes && bytes->tag==V_BYTES && bytes->as.bytes.length==(size_t)length);
        assert(!length || !memcmp(bytes->as.bytes.data,data,(size_t)length));
      } else assert(!decoded->as.variant.payload);
      putchar(valid?'1':'0'); release(&r); memset(&r,0,sizeof(r));
    }
  } else if(mode==21) {
    static const unsigned char bad[]={237,160,128};
    left_value=f_literal(&r,bad,sizeof(bad));
    FValue *failed=f_utf8_encode(&r,NULL,left);
    assert(failed && failed->tag==V_VARIANT && failed->as.variant.tag==0 && !r.error);
    left_value=f_literal(&r,octets,1);
    FValue *nul=f_utf8_encode(&r,NULL,left);
    assert(nul && nul->as.variant.tag==1 && !r.error);
    left_value=f_bytes_literal(&r,NULL,0);
    FValue *empty=f_utf8_decode(&r,NULL,left);
    assert(empty && empty->as.variant.tag==1);
    left_value=force(&r,empty->as.variant.payload);
    assert(left_value && left_value->tag==V_STRING && left_value->as.string.bytes && left_value->as.string.length==0);
    right_value=f_literal(&r,octets,0);
    assert(f_append(&r,NULL,left,right) && !r.error);
    left_value=f_unit(&r); assert(!f_utf8_decode(&r,NULL,left) && r.error);
    r.error=NULL; left_value=f_bytes_literal(&r,octets,1);
    assert(!f_utf8_encode(&r,NULL,left) && r.error);
  } else if(mode==22) {
    assert(!f_utf8_encode(&r,NULL,NULL) && r.error);
    r.error=NULL; left_value=f_literal(&r,NULL,1);
    assert(!f_utf8_encode(&r,NULL,left) && r.error);
    r.error=NULL; left_value=f_literal(&r,octets,1); r.bytes=F_MAX_BYTES;
    assert(!f_utf8_encode(&r,NULL,left) && r.error);
  } else if(mode==23) {
    static const unsigned char valid[]={239,191,189};
    left_value=f_bytes_literal(&r,valid,sizeof(valid)); r.steps=F_MAX_STEPS-2;
    assert(!f_utf8_decode(&r,NULL,left) && r.error);
  } else if(mode==24) {
    size_t lengths[]={0,1,2,4,16,99,256};
    for(size_t i=0;i<sizeof(lengths)/sizeof(lengths[0]);i++) for(size_t n=0;n<259;n++) {
      left_value=number(&r,n);right_value=f_bytes_literal(&r,octets,lengths[i]);
      size_t before=r.bytes;
      FValue *result=f_bytes_length_is(&r,NULL,left,right);
      assert(result && result->tag==V_BOOL && result->as.boolean==(n==lengths[i]) && !r.error);
      assert(r.bytes-before==sizeof(FValue)); /* No unary Nat result allocation. */
      release(&r);memset(&r,0,sizeof(r));
    }
  } else if(mode==25) {
    left_value=f_unit(&r);right_value=f_bytes_literal(&r,NULL,0);
    assert(!f_bytes_length_is(&r,NULL,left,right) && r.error);
    r.error=NULL;left_value=number(&r,0);right_value=f_unit(&r);
    assert(!f_bytes_length_is(&r,NULL,left,right) && r.error);
    r.error=NULL;assert(!f_bytes_length_is(&r,NULL,NULL,right) && r.error);
    r.error=NULL;assert(!f_bytes_length_is(&r,NULL,left,NULL) && r.error);
  } else if(mode==26) {
    left_value=number(&r,1);left_value->as.recursive.tail->value=left_value;
    right_value=f_bytes_literal(&r,NULL,0);r.steps=F_MAX_STEPS-10;
    assert(!f_bytes_length_is(&r,NULL,left,right) && r.error);
  } else if(mode==27) {
    left_value=number(&r,0);right_value=f_bytes_literal(&r,NULL,0);r.bytes=F_MAX_BYTES;
    assert(!f_bytes_length_is(&r,NULL,left,right) && r.error);
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
        for mode in list(range(13)) + list(range(14,20)) + [21,22,23,24,25,26,27]:
            with self.subTest(mode=mode):
                result = subprocess.run([str(self.raw), str(mode)], capture_output=True, timeout=20)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'', b''))

    def test_checked_source_length_predicate(self):
        for n,text,expected in [(0,'','yes'),(1,'','no'),(2,'abc','no'),(3,'abc','yes'),(4,'abc','no')]:
            natural='Zero'
            for _ in range(n):natural='(Succ '+natural+')'
            content=('check : (1 b : Bytes) -> IO Unit\ncheck = \\(1 b : Bytes) => if primBytesLengthIs '+natural+' b then putStrLn "yes" else putStrLn "no"\n'
                'main : IO Unit\nmain = primUTF8Case Bytes (IO Unit) (primUTF8Encode "'+text+'") (putStrLn "invalid") check\n')
            source=self.work/'length.fib';source.write_text(content)
            hosted=run_cli('run',str(source))
            self.assertEqual((hosted.returncode,hosted.stdout,hosted.stderr),(0,expected+'\n',''))
            emitted=run_cli('emit-c',str(source))
            self.assertEqual(emitted.returncode,0,emitted.stderr)
            c=self.work/'length.c';c.write_text(emitted.stdout)
            executable=self.work/'length'
            built=subprocess.run(self.cc+['-std=c11','-Wall','-Wextra','-Werror','-I',str(RUNTIME),str(c),str(RUNTIME/'fibril_runtime.c'),'-o',str(executable)],capture_output=True,timeout=60)
            self.assertEqual(built.returncode,0,built.stderr)
            result=subprocess.run([str(executable)],capture_output=True,timeout=20)
            self.assertEqual((result.returncode,result.stdout,result.stderr),(0,(expected+'\n').encode(),b''))

    def test_utf8_native_matches_python_strict_decoder(self):
        vectors = [b'', *[bytes([a]) for a in range(256)],
            *[bytes([a,b]) for a in range(256) for b in range(256)]]
        vectors += [text.encode('utf-8') for text in ('λ', '🌍', '�', '\ufeff', '\uffff', '\U0010ffff', '\0x')]
        vectors += [bytes.fromhex(text) for text in ('e08080', 'eda080', 'ed9fbf', 'ee8080', 'efbfbf', 'f0908080', 'f0808080', 'f4908080', 'f48fbfbf', 'f5808080', 'e2', 'e282', 'f09f8c')]
        rng = random.Random(7381)
        vectors += [bytes(rng.randrange(256) for _ in range(rng.randrange(9))) for _ in range(1024)]
        expected = bytearray()
        for data in vectors:
            try:
                data.decode('utf-8', errors='strict')
                expected += b'1'
            except UnicodeDecodeError:
                expected += b'0'
        framed = b''.join(bytes([len(data)]) + data for data in vectors)
        result = subprocess.run([str(self.raw), '20'], input=framed, capture_output=True, timeout=30)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (0, bytes(expected), b''))

    def test_native_byte_value_is_not_text_output(self):
        result = subprocess.run([str(self.raw), '13'], capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, b'')
        self.assertIn(b'write expects a string', result.stderr)

    def test_checked_utf8_source_and_console_boundary(self):
        decode = 'decode : (1 b : Bytes) -> IO Unit\ndecode = \\(1 b : Bytes) => primUTF8Case String (IO Unit) (primUTF8Decode b) (putStrLn "invalid") (\\(1 s : String) => putStrLn s)\n'
        truncated = decode.replace('primUTF8Decode b', 'primUTF8Decode (primBytesSlice Zero (Succ Zero) b)')
        cases = [
            ('unicode', (ROOT / 'examples/core/utf8-bytes.fib').read_text(), 'λ 🌍\n'),
            ('empty', decode + 'main : IO Unit\nmain = primUTF8Case Bytes (IO Unit) (primUTF8Encode "") (putStrLn "bad") decode\n', '\n'),
            ('replacement', decode + 'main : IO Unit\nmain = primUTF8Case Bytes (IO Unit) (primUTF8Encode "�") (putStrLn "bad") decode\n', '�\n'),
            ('truncated', truncated + 'main : IO Unit\nmain = primUTF8Case Bytes (IO Unit) (primUTF8Encode "λ") (putStrLn "bad") decode\n', 'invalid\n'),
            ('nul', decode + 'main : IO Unit\nmain = decode (primBytesOctetMod256 Zero)\n', None),
        ]
        for label, content, expected in cases:
            path = self.work / (label + '.fib')
            path.write_text(content)
            for command in ('run', 'run-interactive'):
                with self.subTest(label=label, command=command):
                    result = run_cli(command, str(path))
                    if expected is None:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertNotIn('\0', result.stdout)
                        self.assertIn('NUL', result.stdout + result.stderr)
                    else:
                        self.assertEqual((result.returncode, result.stdout, result.stderr), (0, expected, ''))
            for command in ('emit-c', 'emit-c-interactive'):
                with self.subTest(label=label, command=command):
                    emitted = run_cli(command, str(path))
                    self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
                    self.assertIn('f_utf8_decode(', emitted.stdout)
                    if label != 'nul':
                        self.assertIn('f_utf8_encode(', emitted.stdout)
                    source = self.work / (label + command + '.c')
                    source.write_text(emitted.stdout)
                    executable = self.work / (label + command)
                    compiled = subprocess.run(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror',
                        '-I', str(RUNTIME), str(source), str(RUNTIME / 'fibril_runtime.c'), '-o', str(executable)],
                        capture_output=True, timeout=60)
                    self.assertEqual(compiled.returncode, 0, compiled.stderr.decode(errors='replace'))
                    result = subprocess.run([str(executable)], capture_output=True, timeout=20)
                    if expected is None:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertEqual(result.stdout, b'')
                        self.assertIn(b'NUL', result.stderr)
                    else:
                        self.assertEqual((result.returncode, result.stdout, result.stderr), (0, expected.encode(), b''))

    def test_checked_source_ranges_in_both_modes(self):
        example = 'examples/core/bytes-ranges.fib'
        for command in ('run', 'run-interactive'):
            result = run_cli(command, example)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (0, 'x\n', ''))
        for command in ('emit-c', 'emit-c-interactive'):
            with self.subTest(command=command):
                emitted = run_cli(command, example)
                self.assertEqual(emitted.returncode, 0, emitted.stdout + emitted.stderr)
                self.assertIn('f_bytes_index(', emitted.stdout)
                self.assertIn('f_bytes_slice(', emitted.stdout)
                source = self.work / ('ranges-' + command + '.c')
                source.write_text(emitted.stdout)
                executable = self.work / ('ranges-' + command)
                compiled = subprocess.run(self.cc + ['-std=c11', '-Wall', '-Wextra', '-Werror',
                    '-I', str(RUNTIME), str(source), str(RUNTIME / 'fibril_runtime.c'), '-o', str(executable)],
                    capture_output=True, timeout=60)
                self.assertEqual(compiled.returncode, 0, compiled.stderr.decode(errors='replace'))
                result = subprocess.run([str(executable)], capture_output=True, timeout=20)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b'x\n', b''))

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
