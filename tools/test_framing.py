#!/usr/bin/env python3
"""Bounded Content-Length parsing is Fibril code; this is only a process client."""
import os
from pathlib import Path
import selectors
import shlex
import signal
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
EXE=ROOT/'build/exec/fibril'
SOURCE=ROOT/'examples/modules/binary-frame'
ENTRY=SOURCE/'Main.fib'

# Instrument only the runner, not the Fibril parser or generated program.
ACCOUNTING=r'''
#define fibril_native_binary_run uninstrumented_binary_run
#include "fibril_binary_runtime.c"
#undef fibril_native_binary_run
static FByteStatus counted(FByteSession *session,void *context) {
  size_t requests=session->requests,capacity=session->capacity;
  FByteStatus status=binary_body(session,context);
  fprintf(stderr,"ACCOUNT %zu %zu\n",requests-session->requests,capacity-session->capacity);
  return status;
}
int fibril_native_binary_run(FEval entry,size_t requests,size_t capacity) {
  FRuntime runtime={0};
  FBinaryContext context={&runtime,entry,FB_OK,0,0};
  FByteStatus status=fibril_bytes_run(requests,capacity,stdin,stdout,counted,&context);
  return binary_finish(&runtime,&context,status);
}
'''


def run(command,data=b''):
    process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,start_new_session=True)
    try:
        out,err=process.communicate(data,timeout=30)
        return process.returncode,out,err
    finally:
        if process.poll() is None:
            os.killpg(process.pid,signal.SIGKILL);process.wait()
        for stream in (process.stdin,process.stdout,process.stderr):stream.close()


def frame(data):
    return b'Content-Length: '+str(len(data)).encode()+b'\r\n\r\n'+data


class Framing(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary=tempfile.TemporaryDirectory(prefix='fibril-framing-')
        cls.addClassCleanup(cls.temporary.cleanup)
        work=Path(cls.temporary.name)
        cls.host=[str(EXE),'run-binary','--source-dir',str(SOURCE),str(ENTRY)]
        status,code,err=run([str(EXE),'emit-c-binary','--source-dir',str(SOURCE),str(ENTRY)])
        if status:raise AssertionError(err)
        for name in (b'f_read_bytes(',b'f_write_bytes(',b'f_reject_bytes(',b'f_nominal_case(',b'f_bytes_length_is('):
            if name not in code:raise AssertionError('Missing generated operation '+repr(name))
        source=work/'frame.c';source.write_bytes(code)
        executable=work/'frame'
        runtime=ROOT/'runtime/native'
        built=subprocess.run(shlex.split(os.environ.get('CC','cc'))+['-std=c11','-Wall','-Wextra',
            '-Werror','-I',str(runtime),str(source),str(runtime/'fibril_binary_runtime.c'),'-o',str(executable)],
            capture_output=True,timeout=90)
        if built.returncode:raise AssertionError(built.stderr)
        cls.native=[str(executable)]
        instrumented=work/'accounting.c';instrumented.write_text(ACCOUNTING)
        executable=work/'accounted'
        built=subprocess.run(shlex.split(os.environ.get('CC','cc'))+['-std=c11','-Wall','-Wextra',
            '-Werror','-I',str(runtime),str(source),str(instrumented),'-o',str(executable)],
            capture_output=True,timeout=90)
        if built.returncode:raise AssertionError(built.stderr)
        cls.accounted=[str(executable)]
        second=SOURCE/'Two.fib'
        cls.hostTwo=[str(EXE),'run-binary','--source-dir',str(SOURCE),str(second)]
        status,code,err=run([str(EXE),'emit-c-binary','--source-dir',str(SOURCE),str(second)])
        if status:raise AssertionError(err)
        source=work/'two.c';source.write_bytes(code)
        executable=work/'two'
        built=subprocess.run(shlex.split(os.environ.get('CC','cc'))+['-std=c11','-Wall','-Wextra',
            '-Werror','-I',str(runtime),str(source),str(runtime/'fibril_binary_runtime.c'),'-o',str(executable)],
            capture_output=True,timeout=90)
        if built.returncode:raise AssertionError(built.stderr)
        cls.nativeTwo=[str(executable)]

    def accept(self,data,expected=None):
        expected=data if expected is None else expected
        for command in (self.host,self.native):
            result=run(command,data)
            self.assertEqual(result,(0,expected,b''),(command,result))

    def reject(self,data):
        for command in (self.host,self.native):
            status,out,err=run(command,data)
            self.assertNotEqual(status,0,(command,data,out,err))
            self.assertEqual(out,b'',(command,data,err))
            self.assertIn(b'Binary program rejected input',err)

    def test_small_lengths_and_large_boundaries(self):
        lengths=list(range(100))+[100,101,127,128,255,256,511,512,999,1000,1001,1023,1024,2047,2048,3071,3072,3999]+list(range(4000,4097))
        for n in lengths:
            with self.subTest(n=n):self.accept(frame(bytes(i%256 for i in range(n))))

    def test_bulk_body_request_and_capacity_accounting(self):
        for n,requests in [(0,6),(1,7),(9,7),(10,8),(99,8),(100,9),(999,9),(1000,10),(4096,10)]:
            packet=frame(b'x'*n)
            self.assertEqual(run(self.accounted,packet),(0,packet,f'ACCOUNT {requests} {2*len(packet)}\n'.encode()))
        status,out,err=run(self.accounted,b'Content-Length: 99\r\n\r\n'+b'x')
        self.assertNotEqual(status,0)
        self.assertEqual(out,b'')
        self.assertIn(b'ACCOUNT 6 121\n',err)
        self.assertIn(b'Binary program rejected input',err)
        status,out,err=run(self.accounted,b'Content-Length: 4096\r\n\r\n'+b'x')
        self.assertNotEqual(status,0);self.assertEqual(out,b'')
        self.assertIn(b'ACCOUNT 8 4120\n',err)
        status,out,err=run(self.accounted,b'Content-Length: 4097\r\n\r\n')
        self.assertNotEqual(status,0);self.assertEqual(out,b'')
        self.assertIn(b'ACCOUNT 5 20\n',err)

    def test_all_octets_in_body(self):
        for offset in range(0,256,32):self.accept(frame(bytes(range(offset,offset+32))))

    def test_unicode_count_is_encoded_byte_count(self):
        body='λ 🌍 �'.encode('utf-8')
        self.accept(frame(body))
        self.accept(frame(b'\0\xff\r\n'))

    def test_truncation_at_every_offset(self):
        packet=frame(b'\0\xffab')
        for n in range(len(packet)):
            with self.subTest(n=n):self.reject(packet[:n])

    def test_malformed_and_over_limit_lengths(self):
        for number in (b'',b'-1',b'+1',b'00',b'01',b'09',b'0000',b'0100',b'4097',b'4098',b'4099',b'4100',b'4999',b'5000',b'9999',b'10000',b'9999999999999999999',b'1 ',b' 1',b'1x',b'\xff',b'\0'):
            with self.subTest(number=number):self.reject(b'Content-Length: '+number+b'\r\n\r\n'+b'x'*100)

    def test_short_large_bodies(self):
        for n in (0,1,2,99,100,255,256,999,1000,1024,2048,4095):
            with self.subTest(n=n):self.reject(b'Content-Length: 4096\r\n\r\n'+b'x'*n)

    def test_oversize_rejection_does_not_wait_for_body_or_eof(self):
        for number in (4097,4099,4100,5000,9999,10000):
            for command in (self.host,self.native):
                process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,start_new_session=True)
                try:
                    process.stdin.write(b'Content-Length: '+str(number).encode()+b'\r\n\r\n');process.stdin.flush()
                    self.assertNotEqual(process.wait(timeout=15),0)
                    self.assertEqual(process.stdout.read(),b'')
                    self.assertIn(b'Binary program rejected input',process.stderr.read())
                finally:
                    if process.poll() is None:os.killpg(process.pid,signal.SIGKILL);process.wait()
                    for stream in (process.stdin,process.stdout,process.stderr):stream.close()

    def test_short_99_byte_body_at_every_offset(self):
        for n in range(99):
            with self.subTest(n=n):self.reject(b'Content-Length: 99\r\n\r\n'+b'x'*n)

    def test_header_contract_is_strict(self):
        for prefix in (b'content-length: ',b'Content-length: ',b'Content-Length:',b'Content-Length:  ',b'Other-Length:   '):
            self.reject(prefix+b'1\r\n\r\nx')
        for suffix in (b'\n\n',b'\r\n\n',b'\r\r\n',b'\r\nX\r\n',b'\r\nContent-Length: 1\r\n\r\n'):
            self.reject(b'Content-Length: 1'+suffix+b'x')

    def test_one_frame_leaves_suffix_uninterpreted(self):
        first=frame(b'A')
        self.accept(first+frame(b'B'),first)

    def test_two_frame_sequence_and_later_rejection(self):
        first=frame(b'\0\xff')
        second=frame('λ 🌍'.encode())
        for command in (self.hostTwo,self.nativeTwo):
            self.assertEqual(run(command,first+second),(0,first+second,b''))
            maximum=frame(b'\xff'*4096)
            self.assertEqual(run(command,maximum+maximum),(0,maximum+maximum,b''))
            status,out,err=run(command,first+b'Content-Length: 4097\r\n\r\n')
            self.assertNotEqual(status,0)
            self.assertEqual(out,first)
            self.assertIn(b'Binary program rejected input',err)

    def test_two_frames_flush_each_before_next_input(self):
        packets=(frame(b'A'),frame(bytes(range(256))*16))
        for command in (self.hostTwo,self.nativeTwo):
            process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,start_new_session=True)
            try:
                for packet in packets:
                    process.stdin.write(packet);process.stdin.flush()
                    out=b''
                    with selectors.DefaultSelector() as selector:
                        selector.register(process.stdout,selectors.EVENT_READ)
                        while len(out)<len(packet):
                            self.assertTrue(selector.select(15),'frame flush waited for following frame')
                            part=os.read(process.stdout.fileno(),len(packet)-len(out))
                            self.assertTrue(part,'early EOF in sequence')
                            out+=part
                    self.assertEqual(out,packet)
                self.assertEqual(process.wait(timeout=15),0)
                self.assertEqual(process.stderr.read(),b'')
            finally:
                if process.poll() is None:os.killpg(process.pid,signal.SIGKILL);process.wait()
                for stream in (process.stdin,process.stdout,process.stderr):stream.close()

    def test_fragmented_open_input_completes_without_eof(self):
        packet=frame(bytes(range(256))*16)
        for command in (self.host,self.native):
            process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,start_new_session=True)
            try:
                # Independent writes include splits inside the prefix, decimal,
                # CRLF terminator and body. Keep stdin open after the full frame.
                for piece in (packet[:3],packet[3:16],packet[16:18],packet[18:20],packet[20:22],packet[22:]):
                    process.stdin.write(piece);process.stdin.flush()
                result=b''
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stdout,selectors.EVENT_READ)
                    while len(result)<len(packet):
                        self.assertTrue(selector.select(15),'frame waited for EOF or failed to flush')
                        part=os.read(process.stdout.fileno(),len(packet)-len(result))
                        self.assertTrue(part,'early EOF before echoed frame')
                        result+=part
                self.assertEqual(result,packet)
                self.assertEqual(process.wait(timeout=15),0)
                self.assertEqual(process.stderr.read(),b'')
            finally:
                if process.poll() is None:os.killpg(process.pid,signal.SIGKILL);process.wait()
                for stream in (process.stdin,process.stdout,process.stderr):stream.close()


if __name__=='__main__':unittest.main()
