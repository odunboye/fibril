#!/usr/bin/env python3
"""Oracle regressions, not evidence of Fibril JSON grammar correctness."""
import unittest

from observe_json_state_sharing import check_source_preservation, oracle
from observe_json_combined import category


class JSONOracle(unittest.TestCase):
    def test_state_refactors_preserve_source_logic(self):
        check_source_preservation()

    def test_surrogate_values_are_checked_before_duplicate_overwrite(self):
        for payload in (b'{"a":"\\ud800","a":0}',
                        b'{"a":0,"a":"\\ud800"}',
                        b'{"a":"\\udc00","a":0}',
                        b'{"a":{"x":"\\ud800"},"a":0}',
                        b'{"a":["\\ud800"],"a":0}',
                        b'[{"a":"\\ud800","a":0}]'):
            with self.subTest(payload=payload):
                self.assertEqual(oracle(payload),(True,False,b'\0'))

    def test_surrogate_object_keys_are_checked(self):
        for payload in (b'{"\\ud800":0,"\\ud800":1}',
                        b'{"a":{"\\udc00":0},"a":0}'):
            self.assertEqual(oracle(payload),(True,False,b'\0'))

    def test_valid_duplicate_members_preserve_raw_order(self):
        self.assertEqual(oracle(b'{"a":1,"a":2}'),
            (True,True,b'{S"a"\0:#1\0,S"a"\0:#2\0}'))
        self.assertEqual(oracle(b'{"a":"\\uD834\\uDD1E","a":0}'),
            (True,True,b'{S"a"\0:S"\\uD834\\uDD1E"\0,S"a"\0:#0\0}'))

    def test_arrays_do_not_become_object_member_sequences(self):
        self.assertEqual(oracle(b'[["a",1],["a",2]]'),
            (True,True,b'[[S"a"\0,#1\0],[S"a"\0,#2\0]]'))
        self.assertEqual(oracle(b'[]'),(True,True,b'[]'))
        self.assertEqual(oracle(b'{}'),(True,True,b'{}'))

    def test_observation_does_not_count_budget_failures_as_success(self):
        result={'status':1,'timeout':False,'stdout':b'',
            'stderr':b'fibril native binary: native evaluation budget exhausted\n'}
        self.assertEqual(category(result,b'N',b'null',True),'runtime_blocked')
        result['stderr']+=b'ERROR: AddressSanitizer: heap-buffer-overflow\n'
        self.assertEqual(category(result,b'N',b'null',True),'unexpected_failure')
        result['timeout']=True
        self.assertEqual(category(result,b'N',b'null',True),'timeout')

    def test_observation_requires_exact_output_and_empty_diagnostics(self):
        result={'status':0,'timeout':False,'stdout':b'#1\0','stderr':b''}
        self.assertEqual(category(result,b'#1\0',b'1',True),'match')
        result['stderr']=b'warning'
        self.assertEqual(category(result,b'#1\0',b'1',True),'mismatch')

    def test_invalid_json_and_utf8_remain_failures(self):
        for payload in (b'{"a":}',b'01',b'"\xff"',b'NaN'):
            self.assertEqual(oracle(payload),(False,False,b'\0'))


if __name__=='__main__':unittest.main()
