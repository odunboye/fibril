#!/usr/bin/env python3
"""Embed an actual checked frame validator; no process stdio from embedded code."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples/modules/binary-frame"
HOST = r'''
#include "fibril_binary_embed.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>
typedef struct {
  const unsigned char *input;
  size_t length, consumed, produced, flushes;
  unsigned char output[128];
  int mode;
} Host;
static int read_byte(void *context) {
  Host *h = context;
  if (h->mode == 5 && h->consumed == 2) return -2;
  return h->consumed == h->length ? -1 : h->input[h->consumed++];
}
static int write_byte(void *context, unsigned char byte) {
  Host *h = context;
  if (h->mode == 6 && h->produced == 2) return -1;
  if (h->produced == sizeof(h->output)) return -1;
  h->output[h->produced++] = byte; return 0;
}
static int flush(void *context) {
  Host *h = context; h->flushes++; return h->mode == 7 ? -1 : 0;
}
int main(int argc, char **argv) {
  assert(argc == 2);
  int mode = atoi(argv[1]);
  static const unsigned char valid[] = "Content-Length: 3\r\n\r\n\0\xff\n";
  static const unsigned char empty[] = "Content-Length: 0\r\n\r\n";
  static const unsigned char malformed[] = "Content-Length: 03\r\n\r\nabc";
  static const unsigned char large[] = "Content-Length: 4097\r\n\r\n";
  for (int i = 0; i < 2; i++) {
    Host h = {valid, sizeof(valid) - 1, 0, 0, 0, {0}, mode};
    if (mode == 1) { h.input = empty; h.length = sizeof(empty) - 1; }
    if (mode == 2) { h.input = malformed; h.length = sizeof(malformed) - 1; }
    if (mode == 3) h.length--;
    if (mode == 4) { h.input = large; h.length = sizeof(large) - 1; }
    FByteAdapters host = {read_byte, write_byte, flush, &h};
    FBinaryResult result = fibril_program_binary_embed(&host);
    if (mode == 0 || mode == 1) {
      assert(result.status == F_BINARY_OK && result.message == NULL);
      assert(h.consumed == h.length && h.produced == h.length && h.flushes >= 1);
      assert(!memcmp(h.output, h.input, h.length));
    } else if (mode >= 2 && mode <= 4) {
      assert(result.status == F_BINARY_PROGRAM_ERROR && result.transport_status == FB_OK);
      assert(!strcmp(result.message, "Binary program rejected input"));
      assert(h.produced == 0 && h.flushes == 0);
    } else {
      FByteStatus expected = mode == 5 ? FB_READ_FAILED : mode == 6 ? FB_WRITE_FAILED : FB_FLUSH_FAILED;
      assert(result.status == F_BINARY_TRANSPORT_ERROR && result.transport_status == expected);
      if (mode == 5) assert(h.produced == 0 && h.flushes == 0);
      if (mode == 6) assert(h.produced == 2 && h.flushes == 0 && result.write_prefix == 2);
      if (mode == 7) assert(h.produced == h.length && h.flushes == 1);
    }
  }
  return 0;
}
'''


class GeneratedBinaryEmbeddingTests(unittest.TestCase):
    def test_checked_frame_request_response(self):
        with tempfile.TemporaryDirectory(prefix="fibril-binary-embed-generated-") as directory:
            work = Path(directory)
            generated = subprocess.run([
                str(ROOT / "build/exec/fibril"), "emit-c-binary", "--source-dir",
                str(SOURCE), str(SOURCE / "Main.fib"),
            ], capture_output=True, check=True, timeout=60)
            program = work / "program.c"
            program.write_bytes(generated.stdout)
            host = work / "host.c"
            host.write_text(HOST)
            executable = work / "host"
            common = [*shlex.split(os.environ.get("CC", "cc")), "-std=c11", "-Wall",
                      "-Wextra", "-Werror", "-I", str(ROOT / "runtime/native")]
            runtime = str(ROOT / "runtime/native/fibril_binary_runtime.c")
            subprocess.run([*common, "-DFIBRIL_EMBED_ONLY", str(program), str(host),
                            runtime, "-o", str(executable)], check=True, timeout=60)
            for mode in range(8):
                with self.subTest(mode=mode):
                    result = subprocess.run([str(executable), str(mode)],
                                            capture_output=True, timeout=30)
                    self.assertEqual((result.returncode, result.stdout, result.stderr),
                                     (0, b"", b""))
            # New embedding entry does not change the standalone binary entry.
            subprocess.run([*common, str(program), runtime, "-o", str(executable)],
                           check=True, timeout=60)
            packet = b"Content-Length: 3\r\n\r\n\0\xff\n"
            result = subprocess.run([str(executable)], input=packet,
                                    capture_output=True, timeout=30)
            self.assertEqual((result.returncode, result.stdout, result.stderr),
                             (0, packet, b""))


if __name__ == "__main__":
    unittest.main()
