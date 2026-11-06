#!/usr/bin/env python3
"""Actual checked .fib binary execution and conservative runner separation."""
import os
from pathlib import Path
import selectors
import signal
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


if __name__ == '__main__':
    unittest.main()
