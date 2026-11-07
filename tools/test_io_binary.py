#!/usr/bin/env python3
"""Internal binary transport: real hosted/native byte and failure comparisons."""
import os
import selectors
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
HOST = r'''module BinaryPilot
import Data.List
import System
import System.File
import Tests.Binary
import Tests.BinaryBuffer
import Fibril.Data.Bytes
import Fibril.Runtime.Binary
import Fibril.Runtime.ConsoleInput

code : BinaryError -> String
code BinaryAdmission = "admission"
code BinaryZeroRead = "zero"
code BinaryChunkLimit = "chunk"
code BinaryRequestLimit = "requests"
code BinaryByteLimit = "bytes"
code (BinaryReadFailed captured) = "read:" ++ show (byteLength captured)
code (BinaryWriteFailed count) = "write:" ++ show count
code BinaryFlushFailed = "flush"
code BinaryClosed = "closed"
code BinaryPoisoned = "poisoned"
code BinaryAdapterViolation = "adapter"

echo : Nat -> BinaryTransport -> IO (Either BinaryError ())
echo Z transport = pure (Left BinaryRequestLimit)
echo (S fuel) transport = do
  result <- readBytes 1024 transport
  case result of
    Left err => pure (Left err)
    Right Nothing => pure (Right ())
    Right (Just bytes) => do
      written <- writeBytes bytes transport
      case written of
        Left err => pure (Left err)
        Right () => echo fuel transport

one : Nat -> BinaryTransport -> IO (Either BinaryError ())
one size transport = do
  result <- readBytes size transport
  case result of
    Left err => pure (Left err)
    Right Nothing => pure (Right ())
    Right (Just bytes) => writeBytes bytes transport

bench : Nat -> BinaryTransport -> IO (Either BinaryError ())
bench Z transport = pure (Right ())
bench (S fuel) transport = do
  result <- readBytes 65536 transport
  case result of
    Right (Just bytes) => if byteLength bytes /= 65536 then pure (Left BinaryAdapterViolation) else do
      written <- writeBytes bytes transport
      case written of
        Left err => pure (Left err)
        Right () => bench fuel transport
    _ => pure (Left BinaryAdapterViolation)

body : String -> BinaryTransport -> IO (Either BinaryError ())
body "echo" transport = echo 128 transport
body "bench" transport = bench 64 transport
body "one" transport = one 65536 transport
body "prompt" transport = do
  written <- writeBytes (fromList [0,255]) transport
  case written of
    Left err => pure (Left err)
    Right () => do
      flushed <- flushBytes transport
      case flushed of
        Left err => pure (Left err)
        Right () => one 1 transport
body "mixed" transport = do
  line <- readConsoleLine 32 stdin
  case line of
    Right (Just "header") => one 3 transport
    _ => pure (Left BinaryAdapterViolation)
body "empty" transport = pure (Right ())
body "write-empty" transport = writeBytes empty transport
body "read" transport = do _ <- readBytes 1 transport; pure (Right ())
body "requests" transport = one 1 transport
body "flush" transport = flushBytes transport
body "pair" transport = do
  a <- readBytes 3 transport
  b <- readBytes 3 transport
  case (a, b) of
    (Right (Just first), Right (Just second)) => do
      result <- writeBytes first transport
      case result of
        Left err => pure (Left err)
        Right () => writeBytes second transport
    _ => pure (Left BinaryAdapterViolation)
body "zero" transport = do
  result <- readBytes 0 transport
  if result == Left BinaryZeroRead then one 1 transport else pure (Left BinaryAdapterViolation)
body "oversize" transport = do
  result <- readBytes 65537 transport
  if result == Left BinaryChunkLimit then one 1 transport else pure (Left BinaryAdapterViolation)
body "quota" transport = do
  result <- readBytes 3 transport
  if result == Left BinaryByteLimit then one 1 transport else pure (Left BinaryAdapterViolation)
body "eof-charge" transport = do
  first <- readBytes 2 transport
  case first of
    Right Nothing => do
      next <- readBytes 1 transport
      pure (() <$ next)
    _ => pure (Left BinaryAdapterViolation)
body "short-charge" transport = do
  first <- readBytes 4 transport
  case first of
    Right (Just bytes) => writeBytes bytes transport
    _ => pure (Left BinaryAdapterViolation)
body _ transport = pure (Left BinaryAdapterViolation)

limits : String -> (Nat, Nat)
limits "bench" = (128, 8388608)
limits "empty" = (0, 0)
limits "write-empty" = (1, 0)
limits "one" = (2, 131072)
limits "pair" = (4, 12)
limits "zero" = (2, 2)
limits "oversize" = (2, 2)
limits "quota" = (2, 2)
limits "eof-charge" = (2, 2)
limits "short-charge" = (2, 4)
limits "requests" = (0, 1)
limits "flush" = (0, 0)
limits "admission" = (100001, 0)
limits _ = (256, 262144)

main : IO ()
main = do
  selected <- getEnv "FIBRIL_BINARY_MODE"
  case selected of
    Just "checks" => do
      hosted <- runChecks
      blocks <- runBufferChecks
      let results = checks ++ hosted ++ blocks
      traverse_ (\(label, ok) => putStrLn ((if ok then "PASS: " else "FAIL: ") ++ label)) results
      if all snd results then putStrLn "BINARY_HOSTED_OK" else exitFailure
    Just mode => do
      let (requests, capacity) = limits mode
      adapter <- getEnv "FIBRIL_BINARY_ADAPTER"
      let host = if adapter == Just "reference" then stdioBinaryReference stdin stdout else stdioBinary stdin stdout
      result <- withBinaryAdapters requests capacity host (body mode)
      case result of
        Right () => do _ <- fPutStrLn stderr "ok"; pure ()
        Left err => do _ <- fPutStrLn stderr (code err); exitFailure
    Nothing => exitFailure
'''

NATIVE = r'''#include "fibril_bytes.h"
#include <stdlib.h>
#include <string.h>
static const char *mode;
static FByteStatus one(FByteSession *s, size_t size) {
  FByteRead input = fibril_bytes_read(s, size);
  if (input.status == FB_EOF) return FB_OK;
  if (input.status != FB_OK) return input.status;
  return fibril_bytes_write(s, input.data, input.length, NULL);
}
static FByteStatus body(FByteSession *s, void *unused) {
  (void)unused;
  if (!strcmp(mode,"empty")) return FB_OK;
  if (!strcmp(mode,"write-empty")) return fibril_bytes_write(s,NULL,0,NULL);
  if (!strcmp(mode,"one")) return one(s,65536);
  if (!strcmp(mode,"bench")) {
    for(size_t i=0;i<64;i++) {
      FByteRead input=fibril_bytes_read(s,65536);
      if(input.status!=FB_OK || input.length!=65536) return FB_ADAPTER_VIOLATION;
      FByteStatus result=fibril_bytes_write(s,input.data,input.length,NULL);
      if(result!=FB_OK) return result;
    }
    return FB_OK;
  }
  if (!strcmp(mode,"prompt")) {
    static const unsigned char prompt[]={0,255};
    FByteStatus status=fibril_bytes_write(s,prompt,sizeof(prompt),NULL);
    if(status!=FB_OK) return status;
    status=fibril_bytes_flush(s);
    return status==FB_OK ? one(s,1) : status;
  }
  if (!strcmp(mode,"mixed")) {
    char header[16];
    if(!fgets(header,sizeof(header),stdin) || strcmp(header,"header\n")) return FB_ADAPTER_VIOLATION;
    return one(s,3);
  }
  if (!strcmp(mode,"read")) { (void)fibril_bytes_read(s,1); return FB_OK; }
  if (!strcmp(mode,"requests")) return one(s,1);
  if (!strcmp(mode,"flush")) return fibril_bytes_flush(s);
  if (!strcmp(mode,"zero")) return fibril_bytes_read(s,0).status == FB_ZERO_READ ? one(s,1) : FB_ADAPTER_VIOLATION;
  if (!strcmp(mode,"oversize")) return fibril_bytes_read(s,65537).status == FB_CHUNK_LIMIT ? one(s,1) : FB_ADAPTER_VIOLATION;
  if (!strcmp(mode,"quota")) return fibril_bytes_read(s,3).status == FB_BYTE_LIMIT ? one(s,1) : FB_ADAPTER_VIOLATION;
  if (!strcmp(mode,"eof-charge")) {
    if (fibril_bytes_read(s,2).status != FB_EOF) return FB_ADAPTER_VIOLATION;
    return fibril_bytes_read(s,1).status;
  }
  if (!strcmp(mode,"short-charge")) return one(s,4);
  if (!strcmp(mode,"pair")) {
    FByteRead a=fibril_bytes_read(s,3), b=fibril_bytes_read(s,3);
    if(a.status!=FB_OK || b.status!=FB_OK) return FB_ADAPTER_VIOLATION;
    FByteStatus status=fibril_bytes_write(s,a.data,a.length,NULL);
    return status==FB_OK ? fibril_bytes_write(s,b.data,b.length,NULL) : status;
  }
  for (size_t i=0; i<128; i++) {
    FByteRead input=fibril_bytes_read(s,1024);
    if(input.status==FB_EOF) return FB_OK;
    if(input.status!=FB_OK) return input.status;
    FByteStatus written=fibril_bytes_write(s,input.data,input.length,NULL);
    if(written!=FB_OK) return written;
  }
  return FB_REQUEST_LIMIT;
}
int main(void) {
  mode=getenv("FIBRIL_BINARY_MODE"); if(!mode) return 2;
  size_t requests=256, capacity=262144;
  if(!strcmp(mode,"bench")) { requests=128; capacity=8388608; }
  if(!strcmp(mode,"empty") || !strcmp(mode,"flush")) { requests=0; capacity=0; }
  if(!strcmp(mode,"write-empty")) { requests=1; capacity=0; }
  if(!strcmp(mode,"one")) { requests=2; capacity=131072; }
  if(!strcmp(mode,"pair")) { requests=4; capacity=12; }
  if(!strcmp(mode,"zero") || !strcmp(mode,"oversize") || !strcmp(mode,"quota") || !strcmp(mode,"eof-charge")) { requests=2; capacity=2; }
  if(!strcmp(mode,"short-charge")) { requests=2; capacity=4; }
  if(!strcmp(mode,"requests")) { requests=0; capacity=1; }
  if(!strcmp(mode,"admission")) { requests=100001; capacity=0; }
  FByteStatus status=fibril_bytes_run(requests,capacity,stdin,stdout,body,NULL);
  const char *message="adapter";
  switch(status) {
    case FB_OK: message="ok"; break;
    case FB_ADMISSION: message="admission"; break;
    case FB_ZERO_READ: message="zero"; break;
    case FB_CHUNK_LIMIT: message="chunk"; break;
    case FB_REQUEST_LIMIT: message="requests"; break;
    case FB_BYTE_LIMIT: message="bytes"; break;
    case FB_READ_FAILED: message="read:0"; break;
    case FB_WRITE_FAILED: message="write:0"; break;
    case FB_FLUSH_FAILED: message="flush"; break;
    case FB_POISONED: message="poisoned"; break;
    default: break;
  }
  fprintf(stderr,"%s\n",message);
  return status==FB_OK ? 0 : 1;
}
'''


FAULTS = r'''#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "fibril_bytes.h"
static int mode, allocations, live, reads, writes, flushes, body_calls;
static unsigned char accepted_bytes[4];
static void *allocate_bytes(size_t size) {
  if ((mode==8 && allocations==0) || (mode==9 && allocations==1)) return NULL;
  void *p=malloc(size); if(p) { allocations++; live++; } return p;
}
static void release_bytes(void *p) { if(p) { live--; free(p); } }
#define malloc allocate_bytes
#define free release_bytes
#include "fibril_bytes.c"
#undef malloc
#undef free
#define REQUIRE(x) do { if(!(x)) { fprintf(stderr,"mode %d line %d\n",mode,__LINE__); abort(); } } while(0)
static int read_byte(void *unused) {
  (void)unused; int index=reads++;
  if(mode==1 && index==2) return -2;
  if(mode==5) return 256;
  if(mode==12) return -1;
  return index==0 ? 0 : 255;
}
static int write_byte(void *unused, unsigned char byte) {
  (void)unused; int index=writes++;
  if(mode==2 && index==2) return -1;
  if(mode==6) return 1;
  if(index<4) accepted_bytes[index]=byte;
  return 0;
}
static int flush_bytes(void *unused) {
  (void)unused; flushes++;
  return mode==3 || mode==4 ? -1 : mode==7 ? 1 : 0;
}
static FByteStatus exercise(FByteSession *s, void *unused) {
  (void)unused; body_calls++;
  static const unsigned char data[]={0,255,1};
  size_t count=99;
  if(mode==1) {
    FByteRead r=fibril_bytes_read(s,5);
    REQUIRE(r.status==FB_READ_FAILED && r.length==2 && r.data[0]==0 && r.data[1]==255);
    REQUIRE(fibril_bytes_read(s,1).status==FB_POISONED);
    REQUIRE(fibril_bytes_write(s,data,1,&count)==FB_POISONED && count==0);
    REQUIRE(fibril_bytes_flush(s)==FB_POISONED);
  } else if(mode==2) {
    REQUIRE(fibril_bytes_write(s,data,3,&count)==FB_WRITE_FAILED && count==2);
    REQUIRE(accepted_bytes[0]==0 && accepted_bytes[1]==255);
    REQUIRE(fibril_bytes_read(s,1).status==FB_POISONED);
  } else if(mode==3) {
    REQUIRE(fibril_bytes_flush(s)==FB_FLUSH_FAILED);
    REQUIRE(fibril_bytes_write(s,data,1,NULL)==FB_POISONED);
  } else if(mode==5) {
    REQUIRE(fibril_bytes_read(s,1).status==FB_ADAPTER_VIOLATION);
  } else if(mode==6) {
    REQUIRE(fibril_bytes_write(s,data,1,&count)==FB_ADAPTER_VIOLATION && count==0);
  } else if(mode==8 || mode==9) {
    if(mode==9) { FByteRead r=fibril_bytes_read(s,1); REQUIRE(r.status==FB_OK && r.data[0]==0); }
    REQUIRE(fibril_bytes_read(s,1).status==FB_ALLOCATION_FAILED);
    REQUIRE(fibril_bytes_flush(s)==FB_POISONED);
  } else if(mode==10) {
    REQUIRE(fibril_bytes_write(s,NULL,1,NULL)==FB_ADAPTER_VIOLATION);
  } else if(mode==11) {
    REQUIRE(fibril_bytes_read(s,0).status==FB_ZERO_READ);
    REQUIRE(fibril_bytes_read(s,65537).status==FB_CHUNK_LIMIT);
    REQUIRE(fibril_bytes_write(s,data,65537,NULL)==FB_CHUNK_LIMIT);
    REQUIRE(reads==0 && writes==0 && allocations==0);
  } else if(mode==12) {
    for(size_t i=0;i<128;i++) REQUIRE(fibril_bytes_read(s,65536).status==FB_EOF);
    REQUIRE(fibril_bytes_read(s,1).status==FB_BYTE_LIMIT);
  }
  return FB_OK; /* Faults cannot be swallowed by a trusted callback. */
}
int main(int argc, char **argv) {
  if(argc!=2) return 2; mode=atoi(argv[1]);
  FByteAdapters host={read_byte,write_byte,flush_bytes,NULL};
  FByteStatus result=fibril_bytes_run_with(mode==4 ? 0 : 1000,8388608,host,exercise,NULL);
  FByteStatus expected=FB_OK;
  switch(mode) {
    case 1: expected=FB_READ_FAILED; break;
    case 2: expected=FB_WRITE_FAILED; break;
    case 3: case 4: expected=FB_FLUSH_FAILED; break;
    case 5: case 6: case 7: case 10: expected=FB_ADAPTER_VIOLATION; break;
    case 8: case 9: expected=FB_ALLOCATION_FAILED; break;
  }
  REQUIRE(result==expected && live==0 && body_calls==1);
  if(mode==1) REQUIRE(reads==3 && writes==0 && flushes==0);
  if(mode==2) REQUIRE(reads==0 && writes==3 && flushes==0);
  if(mode==8) REQUIRE(reads==0);
  if(mode==9) REQUIRE(reads==1 && allocations==1);
  if(mode==12) REQUIRE(reads==128 && allocations==128);
  puts("NATIVE_BINARY_OK"); return 0;
}
'''


class BinaryTransport(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="fibril-binary-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.work = Path(cls.directory.name)
        (cls.work / "Fibril").symlink_to(ROOT / "src/Fibril", target_is_directory=True)
        (cls.work / "Tests").symlink_to(ROOT / "test/src/Tests", target_is_directory=True)
        (cls.work / "BinaryPilot.idr").write_text(HOST)
        env = os.environ.copy()
        env.setdefault("CHEZ", shutil.which("chez") or shutil.which("scheme") or "chez")
        built = subprocess.run(shlex.split(env.get("IDRIS2", "idris2")) + ["--source-dir", ".", "--output-dir", "bin", "-o", "host", "BinaryPilot.idr"], cwd=cls.work, env=env, capture_output=True, text=True, timeout=180)
        cls.host = cls.work / "bin/host"
        if built.returncode or not cls.host.exists():
            raise AssertionError(built.stdout + built.stderr)
        (cls.work / "native.c").write_text(NATIVE)
        cls.native = cls.work / "native"
        linked = subprocess.run(shlex.split(env.get("CC", "cc")) + ["-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(ROOT / "runtime/native"), str(cls.work / "native.c"), str(ROOT / "runtime/native/fibril_bytes.c"), "-o", str(cls.native)], capture_output=True, text=True, timeout=60)
        if linked.returncode:
            raise AssertionError(linked.stdout + linked.stderr)
        (cls.work / "faults.c").write_text(FAULTS)
        cls.faults = cls.work / "faults"
        linked = subprocess.run(shlex.split(env.get("CC", "cc")) + ["-std=c11", "-Wall", "-Wextra", "-Werror", "-I", str(ROOT / "runtime/native"), str(cls.work / "faults.c"), "-o", str(cls.faults)], capture_output=True, text=True, timeout=60)
        if linked.returncode:
            raise AssertionError(linked.stdout + linked.stderr)

    def run_mode(self, executable, mode, supplied=b"", adapter="block", timeout=30, **kwargs):
        return subprocess.run([str(executable)], env={**os.environ, "FIBRIL_BINARY_MODE": mode, "FIBRIL_BINARY_ADAPTER": adapter}, input=supplied, capture_output=True, timeout=timeout, **kwargs)

    def compare(self, mode, supplied, expected, code=0, error=b"ok\n"):
        for executable in (self.host, self.native):
            with self.subTest(backend=executable.name, mode=mode):
                result = self.run_mode(executable, mode, supplied)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (code, expected, error))

    def test_native_faults_release_buffers_and_preserve_primary_failures(self):
        for mode in range(1, 13):
            with self.subTest(mode=mode):
                result = subprocess.run([str(self.faults), str(mode)], capture_output=True, timeout=10)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, b"NATIVE_BINARY_OK\n")

    def test_hosted_policy_and_pure_bytes(self):
        result = self.run_mode(self.host, "checks")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(b"BINARY_HOSTED_OK", result.stdout)
        self.assertNotIn(b"FAIL:", result.stdout)

    def test_block_and_reference_host_adapters_agree(self):
        for mode, data in [('echo', bytes(range(256)) * 5), ('one', bytes(range(256)) * 256), ('eof-charge', b''), ('short-charge', b'xx'), ('quota', b'ab'), ('mixed', b'header\n\0\xff\n')]:
            with self.subTest(mode=mode):
                block = self.run_mode(self.host, mode, data)
                reference = self.run_mode(self.host, mode, data, adapter='reference')
                self.assertEqual((block.returncode, block.stdout, block.stderr), (reference.returncode, reference.stdout, reference.stderr))

    def test_roundtrip_all_octets(self):
        data = bytes(range(256))
        self.compare("echo", data, data)

    def test_preserves_invalid_utf8_nul_and_line_endings(self):
        data = b"a\0b\xff\xc0\x80\xed\xa0\x80\r\nlast\r"
        self.compare("echo", data, data)

    def test_utf8_is_not_decoded_or_counted_as_scalars(self):
        data = "λ 🌍 é\r\n".encode()
        self.compare("echo", data, data)

    def test_chunk_boundary_and_short_final_read(self):
        for size in (0, 1, 1023, 1024, 1025, 8193):
            with self.subTest(size=size):
                data = bytes(i % 256 for i in range(size))
                self.compare("echo", data, data)

    def test_maximum_chunk(self):
        data = bytes(range(256)) * 256
        self.compare("one", data, data)

    def test_read_values_survive_subsequent_reads(self):
        self.compare("pair", b"a\0\xffb\xfe\r", b"a\0\xffb\xfe\r")

    def test_invalid_sizes_do_not_consume_input_or_fuel(self):
        for mode in ("zero", "oversize", "quota"):
            self.compare(mode, b"ab", b"a")

    def test_empty_write_and_empty_session(self):
        self.compare("empty", b"", b"")
        self.compare("write-empty", b"", b"")

    def test_request_and_explicit_flush_limits(self):
        self.compare("requests", b"a", b"", 1, b"requests\n")
        self.compare("flush", b"", b"", 1, b"requests\n")

    def test_admission_refuses_session(self):
        self.compare("admission", b"a", b"", 1, b"admission\n")

    def test_eof_and_short_read_reservations_are_not_refunded(self):
        self.compare("eof-charge", b"", b"", 1, b"bytes\n")
        self.compare("short-charge", b"ab", b"", 1, b"bytes\n")

    def test_read_error_is_not_eof_and_cannot_be_ignored(self):
        for executable in (self.host, self.native):
            with self.subTest(backend=executable.name):
                fd = os.open(self.work, os.O_RDONLY)
                try:
                    result = subprocess.run([str(executable)], env={**os.environ, "FIBRIL_BINARY_MODE": "read"}, stdin=fd, capture_output=True, timeout=30)
                finally:
                    os.close(fd)
                self.assertEqual((result.returncode, result.stdout, result.stderr), (1, b"", b"read:0\n"))

    def test_borrowed_text_and_binary_share_stdio_buffering(self):
        self.compare('mixed', b'header\n\0\xff\n', b'\0\xff\n')

    def test_explicit_binary_flush_precedes_blocking_input(self):
        for executable in (self.host, self.native):
            with self.subTest(backend=executable.name):
                process = subprocess.Popen([str(executable)], env={**os.environ, 'FIBRIL_BINARY_MODE': 'prompt'}, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                try:
                    with selectors.DefaultSelector() as selector:
                        selector.register(process.stdout, selectors.EVENT_READ)
                        self.assertTrue(selector.select(timeout=10), 'binary prompt blocked behind input')
                    self.assertEqual(os.read(process.stdout.fileno(), 2), b'\0\xff')
                    output, error = process.communicate(b'X', timeout=10)
                    self.assertEqual((process.returncode, output, error), (0, b'X', b'ok\n'))
                finally:
                    if process.poll() is None:
                        process.kill()
                        process.communicate()

    def test_host_byte_and_transport_constructors_are_private(self):
        env = os.environ.copy()
        for module, ty, constructor in [('ForgeBytes', 'Bytes', 'Packed'), ('ForgeTransport', 'BinaryTransport', 'Transport')]:
            (self.work / f'{module}.idr').write_text(f'module {module}\nimport Fibril.Data.Bytes\nimport Fibril.Runtime.Binary\nbad : {ty}\nbad = {constructor}\n')
            checked = subprocess.run(shlex.split(env.get('IDRIS2', 'idris2')) + ['--source-dir', '.', '--check', f'{module}.idr'], cwd=self.work, capture_output=True, text=True, timeout=60)
            diagnostic = checked.stdout + checked.stderr
            self.assertIn(constructor, diagnostic)
            self.assertTrue(any(word in diagnostic for word in ['private', 'Undefined name', 'not accessible']), diagnostic)

    def test_actual_final_flush_error(self):
        source = self.work / "readonly"
        source.write_bytes(b"unchanged")
        for executable in (self.host, self.native):
            with self.subTest(backend=executable.name), source.open("rb") as readonly:
                result = subprocess.run([str(executable)], env={**os.environ, "FIBRIL_BINARY_MODE": "echo"}, input=b"binary\0\xff", stdout=readonly, stderr=subprocess.PIPE, timeout=30)
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertEqual(result.stderr, b"flush\n")
                self.assertEqual(source.read_bytes(), b"unchanged")


if __name__ == "__main__":
    unittest.main()
