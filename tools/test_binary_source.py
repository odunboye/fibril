#!/usr/bin/env python3
"""Actual checked .fib binary execution and conservative runner separation."""
import os
from pathlib import Path
import selectors
import signal
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / 'build/exec/fibril'


def invoke(command, path, supplied=b'', **kwargs):
    process = subprocess.Popen([str(EXE), command, str(path)], cwd=ROOT,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        start_new_session=True, **kwargs)
    try:
        out, err = process.communicate(supplied, timeout=30)
        return process.returncode, out, err
    finally:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            stream.close()


class SourceBinary(unittest.TestCase):
    def test_single_chunk_eof_short_nul_invalid_utf8(self):
        for data in (b'', b'\0', b'\xff', b'\0\xff', b'\r\n', b'abc'):
            with self.subTest(data=data):
                self.assertEqual(invoke('run-binary', 'examples/core/binary-echo.fib', data), (0, data[:2], b''))

    def test_bounded_sequence_preserves_all_octets(self):
        for offset in range(0,256,32):
            data = bytes(range(offset,offset+32))
            self.assertEqual(invoke('run-binary', 'examples/core/binary-echo-loop.fib', data), (0, data, b''))
        for data in (b'', b'\0\xff\x80\r\n'):
            self.assertEqual(invoke('run-binary', 'examples/core/binary-echo-loop.fib', data), (0, data, b''))

    def test_old_runners_reject_dormant_binary_before_prefix_output(self):
        source = 'main : IO Unit\nmain = do\n  putStrLn "prefix"\n  if True then pure Unit () else primFlushBytes\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'hidden.fib'
            path.write_text(source)
            for command in ('run','run-interactive','emit-c','emit-c-interactive'):
                with self.subTest(command=command):
                    status, out, err = invoke(command, path)
                    self.assertNotEqual(status, 0, (out,err))
                    self.assertNotIn(b'prefix\n', out)
                    self.assertNotIn(b'static FValue', out)

    def test_binary_runner_rejects_dormant_text_before_binary_output(self):
        source = 'main : IO Unit\nmain = do\n  primWriteBytes (primBytesOctetMod256 Zero)\n  if True then pure Unit () else putStrLn "text"\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'mixed.fib'
            path.write_text(source)
            status, out, err = invoke('run-binary', path)
            self.assertNotEqual(status, 0)
            self.assertEqual(out, b'')
            self.assertIn(b'Binary entry rejects', err)

    def test_zero_read_is_a_represented_failure(self):
        source = 'main : IO Unit\nmain = bind ByteReadResult Unit (primReadBytes Zero) (\\(1 r : ByteReadResult) => primByteReadCase (IO Unit) r (pure Unit ()) (\\(1 b : Bytes) => primWriteBytes b))\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'zero.fib'
            path.write_text(source)
            status, out, err = invoke('run-binary', path)
            self.assertNotEqual(status, 0)
            self.assertEqual(out, b'')
            self.assertIn(b'positive capacity', err)

    def test_explicit_flush_visible_before_waiting_for_input(self):
        source = 'main : IO Unit\nmain = do\n  primWriteBytes (primBytesOctetMod256 Zero)\n  primFlushBytes\n  (1 r : ByteReadResult) <- primReadBytes (Succ Zero)\n  primByteReadCase (IO Unit) r (pure Unit ()) (\\(1 b : Bytes) => primWriteBytes b)\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'prompt.fib'
            path.write_text(source)
            process = subprocess.Popen([str(EXE),'run-binary',str(path)], cwd=ROOT,
                stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
            try:
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stdout, selectors.EVENT_READ)
                    self.assertTrue(selector.select(10), 'flush not visible while peer waits')
                    self.assertEqual(os.read(process.stdout.fileno(),1), b'\0')
                out, err = process.communicate(b'\xff',timeout=20)
                self.assertEqual((process.returncode,out,err),(0,b'\xff',b''))
            finally:
                if process.poll() is None:
                    os.killpg(process.pid,signal.SIGKILL)
                    process.wait()
                for stream in (process.stdin,process.stdout,process.stderr):
                    stream.close()

    def test_real_stdin_failure_is_not_eof(self):
        with tempfile.TemporaryDirectory() as directory:
            descriptor = os.open(directory, os.O_RDONLY)
            try:
                process = subprocess.Popen([str(EXE),'run-binary',str(ROOT / 'examples/core/binary-echo.fib')],
                    cwd=ROOT,stdin=descriptor,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
                try:
                    out, err = process.communicate(timeout=20)
                    self.assertNotEqual(process.returncode,0)
                    self.assertEqual(out,b'')
                    self.assertIn(b'Binary read failed',err)
                finally:
                    if process.poll() is None:
                        os.killpg(process.pid,signal.SIGKILL)
                        process.wait()
                    process.stdout.close()
                    process.stderr.close()
            finally:
                os.close(descriptor)

    def test_final_flush_error_is_not_success(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'out.fib'
            path.write_text('main : IO Unit\nmain = primWriteBytes (primBytesOctetMod256 Zero)\n')
            destination = Path(directory) / 'readonly'
            destination.write_bytes(b'')
            with destination.open('rb') as output:
                process = subprocess.Popen([str(EXE),'run-binary',str(path)],cwd=ROOT,
                    stdin=subprocess.DEVNULL,stdout=output,stderr=subprocess.PIPE,start_new_session=True)
                try:
                    _, err = process.communicate(timeout=20)
                    self.assertNotEqual(process.returncode,0)
                    self.assertTrue(b'flush failed' in err or b'write failed' in err,err)
                finally:
                    if process.poll() is None:
                        os.killpg(process.pid,signal.SIGKILL)
                        process.wait()
                    process.stderr.close()


class NativeBinary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='fibril-native-binary-')
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.work = Path(cls.temporary.name)
        cls.cc = shlex.split(os.environ.get('CC','cc'))
        cls.chunk = cls.compile_source(ROOT / 'examples/core/binary-echo.fib', 'chunk')
        cls.loop = cls.compile_source(ROOT / 'examples/core/binary-echo-loop.fib', 'loop')

    @classmethod
    def compile_source(cls, path, name):
        status, source, diagnostic = invoke('emit-c-binary', path)
        if status:
            raise AssertionError(diagnostic)
        if b'fibril_native_binary_run(' not in source or b'f_read_bytes(' not in source:
            raise AssertionError('binary lowering missing from generated C')
        cfile = cls.work / (name + '.c')
        cfile.write_bytes(source)
        executable = cls.work / name
        runtime = ROOT / 'runtime/native'
        compiled = subprocess.run(cls.cc + ['-std=c11','-Wall','-Wextra','-Werror','-I',str(runtime),
            str(cfile),str(runtime / 'fibril_binary_runtime.c'),'-o',str(executable)],
            capture_output=True,timeout=60)
        if compiled.returncode:
            raise AssertionError(compiled.stderr)
        return executable

    def native(self, executable, data):
        result = subprocess.run([str(executable)],input=data,capture_output=True,timeout=20)
        return result.returncode,result.stdout,result.stderr

    def test_hosted_native_chunk_and_sequence_agree(self):
        for data in (b'',b'\0',b'\0\xff',b'\xff\x80\r\nextra'):
            with self.subTest(data=data):
                self.assertEqual(self.native(self.chunk,data),invoke('run-binary','examples/core/binary-echo.fib',data))
        for offset in range(0,256,32):
            data = bytes(range(offset,offset+32))
            self.assertEqual(self.native(self.loop,data),(0,data,b''))
        self.assertEqual(self.native(self.loop,b'\0\xff\x80\r\n'),(0,b'\0\xff\x80\r\n',b''))

    def test_read_views_survive_slice_and_utf8_conversion(self):
        path = self.work / 'views.fib'
        path.write_text('encode : (1 s : String) -> IO Unit\nencode = \\(1 s : String) => primUTF8Case Bytes (IO Unit) (primUTF8Encode s) (pure Unit ()) (\\(1 b : Bytes) => primWriteBytes b)\nhandle : (1 b : Bytes) -> IO Unit\nhandle = \\(1 b : Bytes) => primUTF8Case String (IO Unit) (primUTF8Decode (primBytesSlice Zero (Succ (Succ Zero)) b)) (pure Unit ()) encode\nmain : IO Unit\nmain = bind ByteReadResult Unit (primReadBytes (Succ (Succ Zero))) (\\(1 r : ByteReadResult) => primByteReadCase (IO Unit) r (pure Unit ()) handle)\n')
        executable = self.compile_source(path,'views')
        for data, expected in [(b'\xce\xbb',b'\xce\xbb'),(b'\0a',b'\0a'),(b'\xff\0',b'')]:
            with self.subTest(data=data):
                self.assertEqual(invoke('run-binary',path,data),(0,expected,b''))
                self.assertEqual(self.native(executable,data),(0,expected,b''))

    def test_binary_emitter_rejects_dormant_text(self):
        path = self.work / 'mixed.fib'
        path.write_text('main : IO Unit\nmain = if True then primFlushBytes else putStrLn "text"\n')
        status, out, err = invoke('emit-c-binary',path)
        self.assertNotEqual(status,0)
        self.assertNotIn(b'static FValue',out)
        self.assertIn(b'rejects non-binary',err)

    def test_native_flush_before_input(self):
        path = self.work / 'prompt.fib'
        path.write_text('main : IO Unit\nmain = do\n  primWriteBytes (primBytesOctetMod256 Zero)\n  primFlushBytes\n  (1 r : ByteReadResult) <- primReadBytes (Succ Zero)\n  primByteReadCase (IO Unit) r (pure Unit ()) (\\(1 b : Bytes) => primWriteBytes b)\n')
        executable = self.compile_source(path,'prompt')
        process = subprocess.Popen([str(executable)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        try:
            with selectors.DefaultSelector() as selector:
                selector.register(process.stdout,selectors.EVENT_READ)
                self.assertTrue(selector.select(10),'native flush not visible')
                self.assertEqual(os.read(process.stdout.fileno(),1),b'\0')
            out, err = process.communicate(b'\xff',timeout=20)
            self.assertEqual((process.returncode,out,err),(0,b'\xff',b''))
        finally:
            if process.poll() is None:
                process.kill();process.wait()
            for stream in (process.stdin,process.stdout,process.stderr):
                stream.close()

    def test_native_stdin_and_stdout_failures(self):
        descriptor = os.open(self.work,os.O_RDONLY)
        try:
            result = subprocess.run([str(self.chunk)],stdin=descriptor,capture_output=True,timeout=20)
            self.assertEqual((result.returncode,result.stdout),(1,b''))
            self.assertIn(b'Binary read failed after 0 bytes',result.stderr)
        finally:
            os.close(descriptor)
        destination = self.work / 'readonly'
        destination.write_bytes(b'')
        with destination.open('rb') as output:
            result = subprocess.run([str(self.chunk)],input=b'\0\xff',stdout=output,stderr=subprocess.PIPE,timeout=20)
            self.assertEqual(result.returncode,1)
            self.assertTrue(b'flush failed' in result.stderr or b'write failed' in result.stderr,result.stderr)


if __name__ == '__main__':
    unittest.main()
