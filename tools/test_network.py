#!/usr/bin/env python3
"""Real loopback, checked-source and sanitizer coverage for the POSIX TCP profile."""
import os
from pathlib import Path
import select
import shlex
import socket
import shutil
import time
import subprocess
import tempfile
import threading
import unittest

ROOT = Path(__file__).resolve().parents[1]
CC = shlex.split(os.environ.get('CC', 'cc'))
CLI = ROOT / 'build/exec/fibril'
NATIVE = ROOT / 'runtime/native'


def command(args, **kwargs):
    return subprocess.run([str(x) for x in args], cwd=ROOT, capture_output=True, timeout=120, **kwargs)


def required(result):
    if result.returncode:
        raise AssertionError((result.returncode, result.stdout, result.stderr))
    return result.stdout


class Network(unittest.TestCase):
    def compile(self, directory, source, *, package=False, sanitize=False, source_dir=None):
        output = required(command([CLI, 'emit-c', *(['--package', source] if package else ['--source-dir', source_dir, source] if source_dir else [source])]))
        c = Path(directory) / 'program.c'; c.write_bytes(output)
        exe = Path(directory) / 'program'
        flags = ['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g'] if sanitize else ['-O2', '-fstrict-aliasing']
        required(command([*CC, '-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', *flags,
                          '-I', NATIVE, c, '-o', exe]))
        return exe

    def test_platform_loopback_deadlines_partial_writes_and_cleanup(self):
        for sanitize in (False, True):
            with self.subTest(sanitize=sanitize), tempfile.TemporaryDirectory() as directory:
                exe = Path(directory)/'platform'
                flags = ['-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g'] if sanitize else ['-O2']
                required(command([*CC, '-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic', *flags,
                                  '-I', NATIVE, ROOT/'test/native/network.c', NATIVE/'fibril_network.c', '-o', exe]))
                self.assertIn(b'network platform checks passed', required(command([exe])))

    def test_runtime_cleans_up_after_success_and_late_program_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = Path(directory)/'runtime'
            required(command([*CC, '-std=c11', '-Wall', '-Wextra', '-Werror', '-pedantic',
                              '-fsanitize=address,undefined', '-fno-omit-frame-pointer', '-g',
                              '-I', NATIVE, ROOT/'test/native/network_runtime.c', '-o', exe]))
            self.assertIn(b'network runtime cleanup checks passed', required(command([exe])))

    def test_checked_echo_package_binary_payload_and_eof(self):
        with tempfile.TemporaryDirectory() as directory:
            exe = self.compile(directory, ROOT/'examples/modules/tcp-echo/fibril.yaml', package=True, sanitize=True)
            p = subprocess.Popen([exe], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                self.assertTrue(select.select([p.stdout], [], [], 10)[0], 'listener did not announce its port')
                line = p.stdout.readline(); self.assertTrue(line.strip().isdigit(), line)
                with socket.create_connection(('127.0.0.1', int(line)), timeout=3) as client:
                    payload = b'Fibril\x00\xff\r\n'
                    client.sendall(payload); client.shutdown(socket.SHUT_WR)
                    result = b''
                    while chunk := client.recv(4096): result += chunk
                    self.assertEqual(result, payload)
                output, error = p.communicate(timeout=10)
                self.assertEqual((p.returncode, output, error), (0, str(len(payload)).encode()+b'\n', b''))
            finally:
                if p.poll() is None: p.kill(); p.wait()
                p.stdout.close(); p.stderr.close()

    def test_fibril_read_exactly_fragmentation_eof_timeout_fuel_and_zero(self):
        template = (ROOT/'examples/modules/tcp-client/src/Main.fib').read_text()
        full_fuel = 'Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))'
        cases = [
            ('complete', [b'ab', b'cdefTAIL'], 0.03, None, 6, b'complete:6\n'),
            ('eof', [b'abc'], 0, None, 6, b'eof:3\n'),
            ('fuel', [b'ab', b'cdef'], 0.08, 'Succ Zero', 6, b'exhausted:2\n'),
            ('timeout', [b'ab'], 0.15, None, 6, b'failed:2\n2:0\n'),
            ('zero', [], 0, None, 0, b'complete:0\n'),
            ('no-fuel', [], 0, 'Zero', 6, b'exhausted:0\n'),
            # The 256 KiB cap: at the cap the helper reads (peer closes: eof); above it, nothing is read.
            ('cap-exact', [b'ab'], 0, None, 262144, b'eof:2\n'),
            ('over-cap', [b'ab'], 0, None, 262145, b'exhausted:0\n'),
        ]
        for name, chunks, delay, fuel, count, expected in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                directory=Path(directory);shutil.copytree(ROOT/'stdlib/net/src/Net',directory/'Net')
                listener=socket.socket();self.addCleanup(listener.close);listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(10)
                source=template.replace('5432w',str(listener.getsockname()[1])+'w').replace('socket 6w 1000w',f'socket {count}w {20 if name == "timeout" else 1000}w')
                if fuel is not None:
                    self.assertIn(full_fuel,source);source=source.replace(full_fuel,fuel)
                # A complete result must contain the exact prefix, not merely its length.
                original='Complete bytes => putStrLn (appendString "complete:" (primNetWordToString (primWordFromNat (primBytesLength bytes))))'
                replacement=f'Complete bytes => primUTF8Case String (IO Unit) (primUTF8Decode bytes) (putStrLn "invalid") (\\(1 text : String) => putStrLn (if equalString text "{"abcdef" if count else ""}" then "complete:{count}" else "corrupt"))'
                self.assertIn(original,source);source=source.replace(original,replacement)
                path=directory/'Main.fib';path.write_text(source)
                exe=self.compile(directory,path,source_dir=directory)
                errors=[]
                def serve():
                    try:
                        with listener.accept()[0] as peer:
                            for i,chunk in enumerate(chunks):
                                if i: time.sleep(delay)
                                peer.sendall(chunk)
                            if name=='timeout':time.sleep(delay)
                    except (BrokenPipeError,ConnectionResetError): pass
                    except Exception as error: errors.append(error)
                    finally: listener.close()
                worker=threading.Thread(target=serve,daemon=True);worker.start()
                try:
                    result=command([exe]);self.assertEqual((result.returncode,result.stdout,result.stderr),(0,expected,b''))
                finally:
                    worker.join(timeout=12)
                    self.assertFalse(worker.is_alive(),'peer thread did not finish')
                    self.assertFalse(errors,errors)

    def test_emit_c_selects_network_profile_only_when_sockets_are_used(self):
        plain = required(command([CLI, 'emit-c', ROOT/'examples/core/hello-world.fib']))
        self.assertNotIn(b'fibril_network', plain)
        echo = required(command([CLI, 'emit-c', '--package', ROOT/'examples/modules/tcp-echo/fibril.yaml']))
        self.assertIn(b'#include "fibril_network.c"', echo)
        self.assertNotIn(b'#include "fibril_runtime.h"', echo)
        reader = ('bind ReadResult Unit readLine (\\(1 r : ReadResult) => readCase (IO Unit) r (pure Unit ()) '
                  '(\\(1 t : String) => putStrLn t) (\\(1 m : String) => putStrLn m))')
        # Same dead network branch as the wrong-runner sources, plus console input.
        mixed = ('main : IO Unit\nmain = if True then ' + reader + ' else bind (NetResult Socket) Unit (primNetConnect "127.0.0.1" 1w 0w) '
                 '(\\(1 result : NetResult Socket) => primNetResultCase Socket (IO Unit) result (\\(1 error : NetError) => case error of (1 code : Word) (1 sent : Word) => putStrLn (appendString (primNetWordToString code) (primNetWordToString sent))) '
                 '(\\(1 socket : Socket) => bind (NetResult Unit) Unit (primNetClose socket) (\\(1 result : NetResult Unit) => '
                 'primNetResultCase Unit (IO Unit) result (\\(1 error : NetError) => case error of (1 code : Word) (1 sent : Word) => putStrLn (appendString (primNetWordToString code) (primNetWordToString sent))) (\\(1 value : Unit) => pure Unit value))))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'Main.fib'; path.write_text(mixed)
            required(command([CLI, 'check', path]))
            result = command([CLI, 'emit-c', path])
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn(b'cannot also use console input', result.stdout + result.stderr)

    def test_core_library_checks(self):
        self.assertIn(b'accepted', required(command([CLI, 'check', '--package', ROOT/'stdlib/net/fibril.yaml'])))

    def test_wrong_runner_rejection_including_erased_and_dead_syntax(self):
        sources = [
            'main : IO (NetResult Socket)\nmain = primNetConnect "127.0.0.1" 1w 0w\n',
            'main : IO Unit\nmain = (\\(0 ty : Type) => pure Unit ()) Socket\n',
            'main : IO Unit\nmain = if True then pure Unit () else bind (NetResult Socket) Unit (primNetConnect "127.0.0.1" 1w 0w) (\\(1 result : NetResult Socket) => primNetResultCase Socket (IO Unit) result (\\(1 error : NetError) => case error of (1 code : Word) (1 sent : Word) => putStrLn (appendString (primNetWordToString code) (primNetWordToString sent))) (\\(1 socket : Socket) => bind (NetResult Unit) Unit (primNetClose socket) (\\(1 result : NetResult Unit) => primNetResultCase Unit (IO Unit) result (\\(1 error : NetError) => case error of (1 code : Word) (1 sent : Word) => putStrLn (appendString (primNetWordToString code) (primNetWordToString sent))) (\\(1 value : Unit) => pure Unit value))))\n',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Main.fib'
            for source in sources:
                path.write_text(source)
                required(command([CLI,'check',path]))
                for mode in ['emit-c-embedded','emit-c-binary','emit-js','run','run-binary']:
                    with self.subTest(mode=mode,source=source[:50]):
                        result=command([CLI,mode,path]);self.assertNotEqual(result.returncode,0,result.stdout)

    def test_source_cannot_duplicate_discard_or_mix_handle_kinds(self):
        sources = [
            'bad : (1 socket : Socket) -> IO Unit\nbad socket = pure Unit ()\n',
            'bad : (1 socket : Socket) -> IO SocketWrite\nbad socket = bind (NetResult Unit) SocketWrite (primNetClose socket) (\\(1 ignored : NetResult Unit) => primNetWriteAll socket primBytesEmpty 0w)\n',
            'bad : (1 socket : Socket) -> IO SocketAccept\nbad socket = primNetAccept socket 0w\n',
            'bad : Socket\nbad = 1w\n',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Main.fib'
            for source in sources:
                path.write_text(source+'main : IO Unit\nmain = pure Unit ()\n')
                self.assertNotEqual(command([CLI,'check',path]).returncode,0,source)


if __name__ == '__main__': unittest.main()
