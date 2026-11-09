#!/usr/bin/env python3
"""Checked source -> JavaScript, compared with hosted evaluation and native C."""
import json
import os
from pathlib import Path
import random
import shlex
import shutil
import subprocess
import tempfile
import unittest
from test_cli import ROOT, run_cli
import test_native
import test_native_words

NODE = shlex.split(os.environ.get('NODE', 'node'))

class JavaScriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not NODE or not shutil.which(NODE[0]):
            raise RuntimeError('JavaScript tests require Node.js 18 or newer (NODE may select it)')
        version = subprocess.check_output(NODE + ['--version'], text=True)
        if int(version.lstrip('v').split('.')[0]) < 18:
            raise RuntimeError('JavaScript tests require Node.js 18 or newer')

    def emit(self, args, directory):
        result = run_cli('emit-js', *args, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        path = Path(directory) / "program 'λ'.mjs"
        path.write_text(result.stdout, encoding='utf-8')
        return path

    def node(self, args):
        return subprocess.run(NODE + list(map(str,args)),capture_output=True,timeout=120)

    def compare(self, args, directory, hosted=True):
        path = self.emit(args,directory)
        actual = self.node([path])
        self.assertEqual(actual.returncode,0,actual.stderr)
        _, native = test_native.NativeTests.compile_and_run(self,args,directory)
        self.assertEqual(native.returncode,0,native.stderr)
        self.assertEqual(actual.stdout,native.stdout)
        if hosted:
            reference_args = (['--package',args[1],'--fuel','4096'] if args[0]=='--package'
                              else [*args[:-1],'--fuel','4096',args[-1]])
            reference=run_cli('run',*reference_args,text=False,timeout=120)
            self.assertEqual(reference.returncode,0,reference.stderr)
            self.assertEqual(actual.stdout,reference.stdout)
        return actual.stdout

    def test_runtime_boundaries(self):
        result=self.node([ROOT/'tools/test_javascript_runtime.mjs'])
        self.assertEqual(result.returncode,0,result.stderr)

    def test_core_examples_agree_with_hosted_and_c(self):
        for name in ['javascript','hello-world','console-sequence','io-functions','do-let','do-result',
                     'string-append','bytes-native','bytes-ranges','utf8-bytes','word-native','bytes-equal']:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
                self.compare([str(ROOT/'examples/core'/f'{name}.fib')],directory)

    def test_checked_data_and_recursion_projects_agree_with_hosted_and_c(self):
        for name in ['indexed-vect','index-refinement','mutual-data','nested-data',
                     'native-pairs','record-projections','interfaces','implementation-factories']:
            with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
                source=ROOT/'examples/modules'/name
                self.compare(['--source-dir',str(source),str(source/'Main.fib')],directory)

    def test_word_precision_overflow_and_zero_division_agree(self):
        for name,source in test_native_words.PROGRAMS.items():
            with self.subTest(name=name),tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'Main.fib';path.write_text(source)
                self.compare([str(path)],directory)
        rng=random.Random(7321)
        for index in range(8):
            a,b=rng.getrandbits(64),rng.getrandbits(64)
            expected=(a*b+a)&((1<<64)-1)
            source=f'main : IO Unit\nmain = putStrLn (if primWordEq (primWordAdd (primWordMul {a}w {b}w) {a}w) {expected}w then "ok" else "FAILED")\n'
            with self.subTest(index=index),tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'Main.fib';path.write_text(source)
                self.assertEqual(self.compare([str(path)],directory),b'ok\n')

    def test_standard_library_package_agrees_with_c(self):
        with tempfile.TemporaryDirectory() as directory:
            output=self.compare(['--package',str(ROOT/'stdlib/std/conformance/fibril.yaml')],directory,hosted=False)
            self.assertEqual(output.count(b': ok'),48)
            self.assertNotIn(b'FAILED',output)

    def run_project(self,source):
        """Emit a one-module project as JavaScript and run it; returns (process, node stdout)."""
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)/'src';root.mkdir();path=root/'Main.fib';path.write_text(source)
            program=self.emit(['--source-dir',str(root),str(path)],directory)
            script='const m=await import('+json.dumps(program.resolve().as_uri())+');let out="";try{const used=m.run({write:b=>{out+=new TextDecoder().decode(b)},flush(){}});console.log(JSON.stringify({out,used}));}catch(e){console.log(JSON.stringify({error:String(e.message)}));}'
            result=self.node(['--input-type=module','-e',script]);self.assertEqual(result.returncode,0,result.stderr)
            return json.loads(result.stdout)

    def test_tail_calls_run_in_bounded_depth_and_non_tail_recursion_still_stops(self):
        import test_native_tail
        loop=self.run_project(test_native_tail.LOOP)
        self.assertEqual(loop['out'],'done\n',loop)
        self.assertLess(loop['used']['peakDepth'],64,'2048 tail iterations must not nest (the default cap is 256)')
        lazy=self.run_project(test_native_tail.IGNORED)
        self.assertEqual(lazy['out'],'lazy\n',lazy)
        self.assertLess(lazy['used']['peakDepth'],64)
        deep=self.run_project(test_native_tail.HEADER+test_native_tail.NON_TAIL)
        self.assertEqual(deep.get('error'),'JavaScript depth budget exhausted',deep)

    def test_run_reports_the_resources_it_used(self):
        with tempfile.TemporaryDirectory() as directory:
            path=self.emit([str(ROOT/'examples/core/hello-world.fib')],directory)
            script='const m=await import('+json.dumps(path.resolve().as_uri())+');console.log(JSON.stringify(m.run({write(){},flush(){}})));'
            result=self.node(['--input-type=module','-e',script]);self.assertEqual(result.returncode,0,result.stderr)
            used=json.loads(result.stdout)
            self.assertEqual(sorted(used),['actions','allocatedBytes','peakDepth','steps'])
            self.assertEqual(used['actions'],1)
            self.assertTrue(0<used['peakDepth']<=used['steps'] and used['allocatedBytes']>0,used)

    def test_host_callbacks_imports_and_symlink_launcher(self):
        with tempfile.TemporaryDirectory() as directory:
            path=self.emit([str(ROOT/'examples/core/hello-world.fib')],directory)
            alias=Path(directory)/'alias.mjs';alias.symlink_to(path)
            result=self.node([alias]);self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(result.stdout,b'Hello, world!\n')
            script='const m=await import('+json.dumps(path.resolve().as_uri())+');let lines=[],flushes=0;const host={write:b=>lines.push(new TextDecoder().decode(b)),flush:()=>{flushes++;}};m.run(host);m.run(host);console.log(JSON.stringify({lines,flushes}));'
            result=self.node(['--input-type=module','-e',script]);self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(json.loads(result.stdout),{'lines':['Hello, world!\n']*2,'flushes':2})
            portable='const saved=globalThis.process;globalThis.process=undefined;const m=await import('+json.dumps(path.resolve().as_uri()+'?portable')+');const out=[];m.run({write:b=>out.push(new TextDecoder().decode(b)),flush(){}});globalThis.process=saved;console.log(JSON.stringify(out));'
            result=self.node(['--input-type=module','-e',portable]);self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(json.loads(result.stdout),['Hello, world!\n'])


    def test_source_strings_remain_data(self):
        # Includes supplementary scalars, quotes, backslashes and text that
        # would be executable if concatenated into JavaScript instead of quoted.
        text='"; throw new Error("injected"); // 🌍 λ end\\backslash'
        escaped=text.replace('\\','\\\\').replace('"','\\"')
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Main.fib';path.write_text('main : IO Unit\nmain = putStrLn "'+escaped+'"\n')
            self.assertEqual(self.compare([str(path)],directory),(text+'\n').encode())

    def test_javascript_validates_entire_output_before_callbacks(self):
        source = r'''main : IO Unit
main = do
  putStrLn "must not escape"
  primUTF8Case String (IO Unit) (primUTF8Decode (primBytesOctetMod256 Zero))
    (putStrLn "invalid") (\(1 text : String) => putStrLn text)
'''
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'Main.fib';path.write_text(source)
            emitted=self.emit([str(path)],directory)
            result=self.node([emitted]);self.assertNotEqual(result.returncode,0)
            self.assertEqual(result.stdout,b'')
            self.assertIn(b'console output',result.stderr)

    def test_unsupported_effects_are_rejected_even_when_erased_or_dead(self):
        sources=[
          'main : IO Unit\nmain = if True then putStrLn "safe" else bind ReadResult Unit readLine (\\(1 line : ReadResult) => readCase (IO Unit) line (putStrLn "eof") (\\(1 text : String) => putStrLn text) (\\(1 text : String) => putStrLn text))\n',
          'ignored : (0 input : IO ReadResult) -> IO Unit\nignored input = putStrLn "safe"\nmain : IO Unit\nmain = ignored readLine\n',
          'main : IO Unit\nmain = (\\(0 input : IO ByteReadResult) => putStrLn "safe") (primReadBytes Zero)\n',
        ]
        for source in sources:
            with self.subTest(source=source),tempfile.TemporaryDirectory() as directory:
                path=Path(directory)/'Main.fib';path.write_text(source)
                checked=run_cli('check',str(path));self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
                result=run_cli('emit-js',str(path));self.assertNotEqual(result.returncode,0)
                self.assertEqual(result.stdout,'')
                self.assertIn('JavaScript backend rejects',result.stderr)

    def test_shared_global_dead_input_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root/'Input.fib').write_text('module Input\nexport\nrequest : IO ReadResult\nrequest = readLine\n')
            (root/'Main.fib').write_text('module Main\nimport Input\nignore : (0 input : IO ReadResult) -> IO Unit\nignore input = putStrLn "safe"\nmain : IO Unit\nmain = ignore Input.request\n')
            result=run_cli('emit-js','--source-dir',directory,str(root/'Main.fib'))
            self.assertNotEqual(result.returncode,0)
            self.assertIn('JavaScript backend rejects',result.stderr)
            self.assertEqual(result.stdout,'')

if __name__=='__main__':unittest.main()
