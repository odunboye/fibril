#!/usr/bin/env python3
"""No-heap C profile: object dependencies, trusted arena fixtures and checked source."""
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tempfile
import unittest
from test_cli import ROOT, run_cli
import test_native
import test_native_words

CC=shlex.split(os.environ.get('CC','cc'))
RUNTIME=ROOT/'runtime/native'
COMMON=['-std=c11','-Wall','-Wextra','-Werror','-pedantic','-DFIBRIL_NO_HEAP','-I',str(RUNTIME)]
HOST=r'''
#include "fibril_embedded.h"
#include <stdio.h>
#include <string.h>
static FEmbeddedCell cells[32768];
static unsigned char bytes[262144];
static unsigned char output[65536];
static size_t used, flushes;
static int write_bytes(void *context, const unsigned char *data, size_t length) {
  (void)context;
  if(length>sizeof(output)-used)return 1;
  memcpy(output+used,data,length);used+=length;return 0;
}
static int flush(void *context) { (void)context;flushes++;return 0; }
int main(void) {
  FEmbeddedArena arena={.cells=cells,.cell_capacity=32768,.bytes=bytes,.byte_capacity=sizeof(bytes)};
  FNativeHost host={NULL,write_bytes,flush};
  for(int i=0;i<3;i++) {
    used=0;flushes=0;
    FNativeResult result=fibril_program_embed_arena(&host,&arena);
    if(result.status!=F_NATIVE_OK) { fprintf(stderr,"%s\n",result.message);return 1; }
    if(flushes!=1 || !arena.cells_used || arena.cells_used>arena.cell_capacity || arena.bytes_used>arena.byte_capacity || arena.busy)return 2;
  }
  /* stdio is a test-host adapter, deliberately outside the audited objects. */
  return used && fwrite(output,1,used,stdout)!=used ? 3 : 0;
}
'''
FORBIDDEN=re.compile(r'^(?:malloc|calloc|realloc|free|aligned_alloc|fopen|fclose|fread|fwrite|fputc|fgetc|fflush|fprintf|printf|puts|putchar|getchar|stdin.*|stdout.*|stderr.*|open|close|read|write|exit|abort)$')

class EmbeddedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory(prefix='fibril-embedded-')
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.runtime_object=Path(cls.tmp.name)/'runtime.o'
        cls.build(['-O2','-fstrict-aliasing','-ffreestanding','-fno-builtin','-c',str(RUNTIME/'fibril_runtime.c'),'-o',str(cls.runtime_object)])

    @staticmethod
    def build(args,extra=()):
        result=subprocess.run([*CC,*COMMON,*extra,*args],capture_output=True,timeout=120)
        if result.returncode:raise AssertionError(result.stdout.decode(errors='replace')+result.stderr.decode(errors='replace'))

    def audit(self,path):
        self.assertIsNotNone(shutil.which('nm'),'nm is required for the no-heap object audit')
        result=subprocess.run(['nm','-u',str(path)],capture_output=True,text=True,check=True,timeout=30)
        symbols=[line.split()[-1].lstrip('_') for line in result.stdout.splitlines() if line.split()]
        forbidden=[symbol for symbol in symbols if FORBIDDEN.fullmatch(symbol)]
        self.assertEqual(forbidden,[],result.stdout)

    def test_runtime_has_no_heap_or_stdio_dependencies(self):
        self.audit(self.runtime_object)

    def test_static_memory_sample(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            emitted=run_cli('emit-c-embedded',str(ROOT/'examples/core/embedded.fib'),timeout=120)
            self.assertEqual(emitted.returncode,0,emitted.stdout+emitted.stderr)
            source=root/'program.c';source.write_text(emitted.stdout)
            objects=[]
            for index,path in enumerate([source,ROOT/'examples/native/no_heap.c']):
                obj=root/f'{index}.o'
                self.build(['-O2','-fstrict-aliasing','-ffreestanding','-fno-builtin','-c',str(path),'-o',str(obj)])
                self.audit(obj);objects.append(str(obj))
            executable=root/'sample'
            self.build([*objects,str(self.runtime_object),'-o',str(executable)])
            result=subprocess.run([str(executable)],capture_output=True,timeout=60)
            self.assertEqual((result.returncode,result.stdout,result.stderr),(0,b'',b''))

    def test_typed_pool_contract_and_sanitizers(self):
        for flags in [('-O2','-fstrict-aliasing'),('-fsanitize=address,undefined','-fno-omit-frame-pointer','-g')]:
            with self.subTest(flags=flags),tempfile.TemporaryDirectory() as directory:
                executable=Path(directory)/'contract'
                self.build([str(ROOT/'test/native/embedded.c'),str(RUNTIME/'fibril_runtime.c'),'-o',str(executable)],flags)
                result=subprocess.run([str(executable)],capture_output=True,timeout=60)
                self.assertEqual((result.returncode,result.stdout,result.stderr),(0,b'',b''))

    def compare(self,args,*,hosted=True):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            emitted=run_cli('emit-c-embedded',*args,timeout=120)
            self.assertEqual(emitted.returncode,0,emitted.stdout+emitted.stderr)
            self.assertNotIn('int main(',emitted.stdout)
            self.assertIn('fibril_program_embed_arena',emitted.stdout)
            source=root/'program.c';source.write_text(emitted.stdout)
            obj=root/'program.o';host=root/'host.c';host.write_text(HOST)
            self.build(['-O2','-fstrict-aliasing','-ffreestanding','-fno-builtin','-c',str(source),'-o',str(obj)])
            self.audit(obj)
            executable=root/'program'
            self.build([str(obj),str(host),str(self.runtime_object),'-o',str(executable)])
            result=subprocess.run([str(executable)],capture_output=True,timeout=120)
            self.assertEqual(result.returncode,0,result.stderr)
            _,native=test_native.NativeTests.compile_and_run(self,args,root)
            self.assertEqual(native.returncode,0,native.stderr)
            self.assertEqual(result.stdout,native.stdout)
            if hosted:
                refargs=['--package',args[1],'--fuel','4096'] if args[0]=='--package' else [*args[:-1],'--fuel','4096',args[-1]]
                reference=run_cli('run',*refargs,text=False,timeout=120)
                self.assertEqual(reference.returncode,0,reference.stderr)
                self.assertEqual(result.stdout,reference.stdout)
            return result.stdout

    def test_checked_core_examples_match_hosted_and_hosted_c(self):
        for name in ['hello-world','javascript','console-sequence','do-result','bytes-native','bytes-ranges','utf8-bytes','word-native']:
            with self.subTest(name=name):self.compare([str(ROOT/'examples/core'/f'{name}.fib')])

    def test_checked_families_and_recursion_match(self):
        for name in ['index-refinement','indexed-vect','mutual-data','nested-data','native-pairs']:
            with self.subTest(name=name):
                root=ROOT/'examples/modules'/name
                self.compare(['--source-dir',str(root),str(root/'Main.fib')])

    def test_word_precision_division_and_wraparound_match(self):
        for name,source in test_native_words.PROGRAMS.items():
            with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'Main.fib';path.write_text(source)
                self.compare([str(path)])

    def test_application_package_matches_hosted_c(self):
        output=self.compare(['--package',str(ROOT/'stdlib/std/conformance/fibril.yaml')],hosted=False)
        self.assertEqual(output.count(b': ok'),24)

    def test_regions_copy_results_without_region_lifetime_escape(self):
        source=r'''module Main
both : (s : String) -> String
both s = appendString (primWithRegion String (\(0 r : Type) => appendString s "-in")) s
main : IO Unit
main = putStrLn (both (appendString "a" "b"))
'''
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Main.fib';path.write_text(source)
            self.assertEqual(self.compare(['--source-dir',directory,str(path)]),b'ab-inab\n')

    def test_unsupported_requests_are_rejected_before_emission(self):
        for source in [
            'ignore : (0 input : IO ReadResult) -> IO Unit\nignore input = putStrLn "safe"\nmain : IO Unit\nmain = ignore readLine\n',
            'main : IO Unit\nmain = (\\(0 input : IO ByteReadResult) => putStrLn "safe") (primReadBytes Zero)\n',
        ]:
            with self.subTest(source=source),tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'Main.fib';path.write_text(source)
                checked=run_cli('check',str(path));self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
                result=run_cli('emit-c-embedded',str(path));self.assertNotEqual(result.returncode,0)
                self.assertEqual(result.stdout,'');self.assertIn('Embedded profile rejects',result.stderr)

    def test_profile_flag_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)/'wrong.c';source.write_text('#include "fibril_embedded.h"\n')
            result=subprocess.run([*CC,'-std=c11','-I',str(RUNTIME),'-c',str(source),'-o',str(Path(directory)/'x.o')],capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('FIBRIL_NO_HEAP',result.stderr)

if __name__=='__main__':unittest.main()
