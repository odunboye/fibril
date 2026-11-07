#!/usr/bin/env python3
"""Probe validity/classification checks; limits are observations, not golden failures."""
from pathlib import Path
import tempfile
import unittest

from bench_binary_numbers import EXE, classify, invoke, native_observation, program


class NumericProbes(unittest.TestCase):
    def test_success_requires_exact_output_and_empty_stderr(self):
        result={'status':0,'timeout':False,'seconds':0,'stdout':b'abc','stderr':b''}
        self.assertEqual(classify(result,b'abc')['outcome'],'ok')
        self.assertEqual(classify(result,b'ab')['outcome'],'incorrect-output')
        result['stderr']=b'warning'
        self.assertEqual(classify(result,b'abc')['outcome'],'incorrect-output')

    def test_failures_are_not_equivalence_success(self):
        result={'status':1,'timeout':False,'seconds':0,'stdout':b'',
            'stderr':b'Binary reduction budget exhausted'}
        self.assertEqual(classify(result,b'')['outcome'],'bounded-rejection')
        result['stderr']=b'Binary reduction budget exhausted\nERROR: AddressSanitizer: heap-buffer-overflow'
        self.assertEqual(classify(result,b'')['outcome'],'error')
        result['stderr']=b'Parsing: bad fixture'
        self.assertEqual(classify(result,b'')['outcome'],'error')
        result['status']=-9
        self.assertEqual(classify(result,b'')['outcome'],'signal')
        result['timeout']=True
        self.assertEqual(classify(result,b'')['outcome'],'timeout')

    def test_native_counters_do_not_hide_program_diagnostics(self):
        result={'status':0,'timeout':False,'seconds':0,'stdout':b'x',
            'stderr':b'FIBRIL_NUMERIC_METRICS 123 456 100000 512\n'}
        observed=native_observation(result,b'x')
        self.assertEqual(observed['outcome'],'ok')
        self.assertEqual(observed['evaluator_steps'],123)
        self.assertEqual(observed['arena_payload_bytes'],456)
        result['status']=1
        result['stderr']+=b'fibril native binary: native evaluation budget exhausted\n'
        observed=native_observation(result,b'x')
        self.assertEqual(observed['outcome'],'bounded-rejection')
        self.assertEqual(observed['native_limit'],'depth')
        result['stderr']=result['stderr'].replace(b'123 456',b'100000 456')
        self.assertEqual(native_observation(result,b'x')['native_limit'],'steps')

    def test_generator_rejects_out_of_policy_inputs(self):
        for n in (0,4097):
            with self.assertRaises(ValueError):program(n,'decimal',True)
        with self.assertRaises(ValueError):program(1,'unknown',True)

    def test_all_count_constructions_have_actual_checked_source(self):
        with tempfile.TemporaryDirectory(prefix='fibril-number-test-') as tmp:
            source=Path(tmp)/'Probe.fib'
            for method in ('decimal','decimal-fold','byte-count','byte-decimal'):
                with self.subTest(method=method):
                    source.write_text(program(99,method,True))
                    data=bytes(range(99))
                    result=invoke([str(EXE),'run-binary','--source-dir',tmp,str(source)],data)
                    self.assertEqual(classify(result,data)['outcome'],'ok',result['stderr'])

    def test_force_shared_byte_decimal_reaches_4k(self):
        with tempfile.TemporaryDirectory(prefix='fibril-number-4k-test-') as tmp:
            source=Path(tmp)/'Probe.fib';source.write_text(program(4096,'byte-decimal',True))
            data=bytes(range(256))*16
            result=invoke([str(EXE),'run-binary','--source-dir',tmp,str(source)],data)
            self.assertEqual(classify(result,data)['outcome'],'ok',result['stderr'])


if __name__=='__main__':unittest.main()
