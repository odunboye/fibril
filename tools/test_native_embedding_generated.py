#!/usr/bin/env python3
"""Check a real Fibril program through the generated embedding entry point."""
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
HOST = r'''
#include "fibril_runtime.h"
#include <assert.h>
#include <string.h>
typedef struct { unsigned char bytes[64]; size_t length, flushes; } Sink;
static int write_bytes(void *context, const unsigned char *bytes, size_t length) {
  Sink *s = context;
  if (length > sizeof(s->bytes) - s->length) return 1;
  memcpy(s->bytes + s->length, bytes, length); s->length += length; return 0;
}
static int flush(void *context) { ((Sink *)context)->flushes++; return 0; }
int main(void) {
  for (int i = 0; i < 3; i++) {
    Sink s = {0}; FNativeHost host = { &s, write_bytes, flush };
    FNativeResult result = fibril_program_embed(&host);
    assert(result.status == F_NATIVE_OK && result.message == NULL);
    assert(s.length == 13 && !memcmp(s.bytes, "hello worker\n", 13));
    assert(s.flushes == 1);
  }
  return 0;
}
'''


class GeneratedEmbeddingTests(unittest.TestCase):
    def test_checked_program(self):
        compiler = shlex.split(os.environ.get("CC", "cc"))
        with tempfile.TemporaryDirectory(prefix="fibril-embed-generated-") as directory:
            directory = Path(directory)
            source = directory / "Main.fib"
            source.write_text('main : IO Unit\nmain = putStrLn "hello worker"\n')
            generated = subprocess.run([str(ROOT / "build/exec/fibril"), "emit-c", str(source)],
                                       capture_output=True, check=True, timeout=60)
            program = directory / "program.c"
            program.write_bytes(generated.stdout)
            host = directory / "host.c"
            host.write_text(HOST)
            executable = directory / "host"
            common = [*compiler, "-std=c11", "-Wall", "-Wextra", "-Werror",
                      "-I", str(ROOT / "runtime/native")]
            runtime = str(ROOT / "runtime/native/fibril_runtime.c")
            subprocess.run([*common, "-DFIBRIL_EMBED_ONLY", str(program), str(host),
                            runtime, "-o", str(executable)], check=True, timeout=60)
            result = subprocess.run([str(executable)], capture_output=True, timeout=30)
            self.assertEqual((result.returncode, result.stdout, result.stderr), (0, b"", b""))
            # The same emitted file still works as the legacy standalone CLI.
            subprocess.run([*common, str(program), runtime, "-o", str(executable)],
                           check=True, timeout=60)
            result = subprocess.run([str(executable)], capture_output=True, timeout=30)
            self.assertEqual((result.returncode, result.stdout, result.stderr),
                             (0, b"hello worker\n", b""))


if __name__ == "__main__":
    unittest.main()
