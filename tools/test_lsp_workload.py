#!/usr/bin/env python3
"""OFFLINE corpus/evidence checks; recorded cap denials are not parser passes."""
import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from generate_lsp_workload import (DESTINATION, ROOT, SOURCE, ObjectMembers, artifacts,
                                   bodies, describe, frame)
from observe_json_state_sharing import oracle
from probe_lsp_workload import checked, observation, run_process


class LSPWorkload(unittest.TestCase):
    def test_committed_corpus_is_exact_and_reproducible(self):
        expected = artifacts()
        actual = {p.name: p.read_bytes() for p in DESTINATION.iterdir() if p.is_file()}
        self.assertEqual(actual, expected)
        self.assertEqual(artifacts(), expected)
        self.assertEqual(len(list(bodies())), 14)
        for name, body, provenance in bodies():
            with self.subTest(case=name):
                self.assertEqual(actual[name + '.frame'], frame(body))
                header, payload = actual[name + '.frame'].split(b'\r\n\r\n', 1)
                self.assertEqual(header, b'Content-Length: ' + str(len(payload)).encode())
                self.assertEqual(payload, body)
                self.assertFalse(describe(name, body, provenance)['captured_client_traffic'])

    def test_duplicate_fields_and_id_kinds_remain_ordered(self):
        rows = {r['name']: r for r in json.loads(artifacts()['manifest.json'])['cases']}
        duplicate = rows['duplicate-fields']
        self.assertEqual(duplicate['expected_id_kinds'], ['string', 'number'])
        self.assertEqual(duplicate['expected_id_values'], ['s-1', 7])
        self.assertEqual(duplicate['expected_fields']['object_members'][-1],
                         ['params', {'object_members': [['x', 1], ['x', 2]]}])
        self.assertEqual(duplicate['envelope_policy'], 'ambiguous-duplicate-id-no-dispatch-expectation')
        self.assertEqual(rows['initialized']['expected_id_kinds'], ['absent'])
        self.assertEqual(rows['shutdown']['expected_id_kinds'], ['number'])
        self.assertEqual(rows['shutdown-string-id']['expected_id_kinds'], ['string'])
        for invalid in (b'{"x":"\\ud800","x":0}', b'{"x":0,"x":{"y":"\\ud800"}}'):
            with self.assertRaises(UnicodeError):
                describe('invalid', invalid, 'synthetic')
        with self.assertRaises(ValueError):
            describe('invalid', b'{"x":}', 'synthetic')

    def test_ordered_utf16_edits_nonascii_and_crlf(self):
        body = dict((name, data) for name, data, _ in bodies())['didChange-utf16']
        changes = json.loads(body)['params']['contentChanges']
        text = SOURCE
        for change in changes:
            span = change['range']
            self.assertEqual(span['start']['line'], span['end']['line'])
            lines = text.splitlines(keepends=True)
            index = span['start']['line']
            raw = lines[index].encode('utf-16-le')
            start, end = 2 * span['start']['character'], 2 * span['end']['character']
            # Strict decode ensures no edit splits a surrogate pair.
            replaced = raw[start:end].decode('utf-16-le')
            self.assertEqual(len(replaced.encode('utf-16-le')) // 2, change['rangeLength'])
            lines[index] = (raw[:start].decode('utf-16-le') + change['text'] + raw[end:].decode('utf-16-le'))
            text = ''.join(lines)
        self.assertEqual(text, 'main : IO Unit\r\nmain = putStrLn "α🧵λé"\r\n')
        self.assertGreater(len(body), len(body.decode()))

    def test_boundaries_tokens_nesting_and_realistic_capabilities(self):
        rows = {r['name']: r for r in json.loads(artifacts()['manifest.json'])['cases']}
        for n in (4095, 4096, 4097):
            row = rows[f'didOpen-boundary-{n}']
            self.assertEqual(row['body_bytes'], n)
            self.assertEqual(row['wire_bytes'], n + 24)
            self.assertEqual(row['canonical_framer_policy'], 'within-4096-body-cap' if n <= 4096 else 'over-4096-body-cap')
        capabilities = rows['initialize-capabilities']
        self.assertEqual((capabilities['body_bytes'], capabilities['tokens'], capabilities['max_container_nesting']), (3681, 720, 8))
        self.assertGreater(capabilities['tokens'], 512)  # Not silently an accepted policy.
        self.assertGreater(rows['didOpen-large']['body_bytes'], 4096)
        self.assertGreater(rows['didChange-large']['body_bytes'], 4096)
        duplicate = json.loads(dict((n, b) for n, b, _ in bodies())['duplicate-fields'], object_pairs_hook=ObjectMembers)
        self.assertEqual([item for key, item in duplicate if key == 'id'], ['s-1', 7])

    def test_committed_evidence_accounting_and_oracle(self):
        evidence = json.loads((ROOT / 'docs/assets/evidence/lsp-workload.json').read_text())
        self.assertEqual(evidence['corpus_manifest_sha256'], hashlib.sha256(artifacts()['manifest.json']).hexdigest())
        self.assertEqual(len(evidence['production_source_sha256']), 8)
        for path, digest in evidence['production_source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), digest, path)
        inputs = {name: body for name, body, _ in bodies()}
        inputs.update({'control-tokens64': b'[' + b','.join([b'[]'] + [b'0'] * 30) + b']',
                       'control-string64': b'"' + b'a' * 62 + b'"',
                       'control-utf8-string64': ('"' + 'ÿ' * 31 + '"').encode(),
                       'control-padded64': b' ' * 63 + b'1'})
        self.assertEqual(len(evidence['rows']), 64)
        self.assertEqual(len({(r['consumer'], r['case'], r['backend']) for r in evidence['rows']}), 64)
        for row in evidence['rows']:
            body = inputs[row['case']]
            native = row['native_metrics']
            self.assertFalse(row['whole_jsonrpc_decoded'])
            if row['consumer'] == 'canonical-frame':
                self.assertFalse(row['whole_json_body_parsed'])
                accepted = len(body) <= 4096
                output = frame(body) if accepted else b''
                self.assertEqual(row['exit_code'], 0 if accepted else 1)
                if native:
                    self.assertEqual(native['consumed_bytes'], len(frame(body)) if accepted else 20)
                    self.assertEqual(native['reserved_capacity'], 2 * len(frame(body)) if accepted else 20)
                    self.assertEqual(native['flushes'], 2 if accepted else 0)
            else:
                output = oracle(body[:65])[2]
                self.assertEqual(row['exit_code'], 0)
                self.assertEqual(row['whole_json_body_parsed'], len(body) <= 64)
                if native:
                    self.assertEqual(native['consumed_bytes'], min(len(body), 65))
                    self.assertEqual(native['callbacks'], len(body) + 1 if len(body) <= 64 else 0)
                    self.assertEqual(native['reserved_capacity'], 65 + len(output))
                    self.assertEqual(native['requests'], 2)
                if len(body) > 64:
                    self.assertEqual(row['outcome'], 'json-diagnostic-cap-denial-not-whole-body-parsing')
            self.assertEqual(row['output_bytes'], len(output))
            self.assertEqual(row['output_sha256'], hashlib.sha256(output).hexdigest())
            if native:
                self.assertEqual(native['accepted_bytes'], len(output))
                self.assertLess(native['steps'], 100000)
                self.assertLess(native['arena_payload'], 16 * 1024 * 1024)
            else:
                self.assertEqual(row['backend'], 'hosted')
        self.assertEqual([r['core_nodes'] for r in evidence['admission']], [4341, 8002, 7467])

    def test_normal_and_sanitized_evidence_agree(self):
        normal = json.loads((ROOT / 'docs/assets/evidence/lsp-workload.json').read_text())
        sanitized = json.loads((ROOT / 'docs/assets/evidence/lsp-workload-sanitized.json').read_text())
        self.assertIn('-fsanitize=address,undefined', sanitized['cc'])
        self.assertEqual(normal['rows'], sanitized['rows'])
        self.assertEqual(normal['admission'], sanitized['admission'])
        self.assertEqual(normal['corpus_manifest_sha256'], sanitized['corpus_manifest_sha256'])
        self.assertEqual(normal['production_source_sha256'], sanitized['production_source_sha256'])
        self.assertEqual(normal['compiler_sha256'], sanitized['compiler_sha256'])
        for evidence in (normal, sanitized):
            # Historical launcher digest, not a reconstructed compiler-image hash.
            self.assertEqual(evidence['compiler_sha256'],
                             '8587e4e519ac3367e035c863c845899210988d1ad39551700425b44b1fda6156')
            self.assertEqual(evidence['compiler_sha256_scope'],
                             'launcher file bytes only; compiler image not recorded')
            self.assertNotIn('compiler_image_sha256', evidence)

    def test_observer_metrics_sanitizer_and_timeout_fail_closed(self):
        result = subprocess.CompletedProcess([], 0, b'ok', b'PROFILE 1 2 3 4 5 6 7 8 9 10 11\n')
        with patch('probe_lsp_workload.run_process', return_value=result):
            code, output, diagnostic, metrics = observation(['unused'], b'', 1)
            self.assertEqual((code, output, diagnostic), (0, b'ok', ''))
            self.assertEqual(metrics['consumed_bytes'], 7)
            self.assertEqual(metrics['reserved_capacity'], 11)
        with patch('probe_lsp_workload.run_process', side_effect=subprocess.TimeoutExpired('unused', 1)):
            with self.assertRaises(subprocess.TimeoutExpired):
                observation(['unused'], b'', 1)
        result.stderr = b'runtime error: invalid memory access\n'
        with patch('probe_lsp_workload.run_process', return_value=result):
            with self.assertRaises(AssertionError):
                observation(['unused'], b'', 1)


# Only test processes are launched. A Unix-socket handshake proves the child
# installed SIG_IGN before timeout/cancellation; EOF proves its socket died.
# No sleeps, process polling, or compiler/baseline execution is used here.
PROCESS_TREE = r'''
import signal, subprocess, sys
signal.signal(signal.SIGTERM, signal.SIG_IGN)
child = r"""
import json, os, signal, socket, sys
signal.signal(signal.SIGTERM, signal.SIG_IGN)
with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as ready:
    ready.connect(sys.argv[1])
    ready.sendall((json.dumps({'pid': os.getpid(), 'group': os.getpgrp()}) + '\n').encode())
    signal.pause()
"""
subprocess.Popen([sys.executable, '-c', child, sys.argv[1]],
                 stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
if sys.argv[2] == 'exit':
    sys.exit(0)
signal.pause()
'''


class ProbeProcessScope(unittest.TestCase):
    def exercise_tree(self, *, exited_leader=False, cancellation=None):
        real_popen, real_killpg = subprocess.Popen, os.killpg
        processes, connections, signals = [], [], []
        with tempfile.TemporaryDirectory(prefix='lsp-probe-process-', dir='/tmp') as temporary:
            # macOS Unix sockets have a short path limit; /tmp avoids long TMPDIR.
            path = str(Path(temporary) / 'ready.sock')
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
                listener.settimeout(5)
                listener.bind(path)
                listener.listen(1)

                def launch(*args, **kwargs):
                    self.assertTrue(kwargs['start_new_session'])
                    process = real_popen(*args, **kwargs)
                    processes.append(process)
                    communicate = process.communicate

                    def after_handshake(**options):
                        connection, _ = listener.accept()
                        connections.append(connection)
                        connection.settimeout(5)
                        with connection.makefile('rb') as stream:
                            ready = json.loads(stream.readline(1024))
                        self.assertNotEqual(ready['pid'], process.pid)
                        self.assertEqual(ready['group'], process.pid)
                        if exited_leader:
                            self.assertEqual(process.wait(timeout=5), 0)
                        if cancellation is not None:
                            raise cancellation
                        return communicate(**options)

                    process.communicate = after_handshake
                    return process

                def signal_owned(group, signum):
                    self.assertEqual(group, processes[0].pid)
                    self.assertNotEqual(group, os.getpgrp())
                    signals.append(signum)
                    real_killpg(group, signum)

                command = [sys.executable, '-c', PROCESS_TREE, path, 'exit' if exited_leader else 'wait']
                cleanup_verified = False
                try:
                    with patch('probe_lsp_workload.subprocess.Popen', side_effect=launch), \
                         patch('probe_lsp_workload.os.killpg', side_effect=signal_owned):
                        if cancellation is not None:
                            with self.assertRaises(type(cancellation)) as raised:
                                run_process(command, timeout=0.05)
                            self.assertIs(raised.exception, cancellation)
                        elif exited_leader:
                            self.assertEqual(run_process(command, timeout=1).returncode, 0)
                        else:
                            with self.assertRaises(subprocess.TimeoutExpired):
                                run_process(command, timeout=0.05)
                    self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
                    self.assertEqual(connections[0].recv(1), b'')
                    self.assertIsNotNone(processes[0].returncode)
                    self.assertEqual(processes[0].wait(timeout=1), 0 if exited_leader else -signal.SIGKILL)
                    cleanup_verified = True
                    self.assertTrue(all(stream.closed for stream in
                                        (processes[0].stdin, processes[0].stdout, processes[0].stderr)))
                finally:
                    # Fallback only when termination/reaping was not verified;
                    # do not signal a completed, reaped group's old id again.
                    for process in processes:
                        if not cleanup_verified:
                            try:
                                real_killpg(process.pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                        process.wait(timeout=2)
                        for stream in (process.stdin, process.stdout, process.stderr):
                            stream.close()
                    for connection in connections:
                        connection.close()

    def test_timeout_kills_term_ignoring_descendant_and_reaps_leader(self):
        self.exercise_tree()

    def test_exited_leader_does_not_skip_descendant_kill(self):
        self.exercise_tree(exited_leader=True)

    def test_cancellation_and_baseexception_cleanup(self):
        class Cancelled(BaseException):
            pass
        for cancellation in (KeyboardInterrupt(), SystemExit(17), Cancelled()):
            with self.subTest(cancellation=type(cancellation).__name__):
                self.exercise_tree(cancellation=cancellation)

    def test_success_and_failure_preserve_process_results(self):
        result = run_process([sys.executable, '-c',
                              'import sys; sys.stdout.buffer.write(sys.stdin.buffer.read()); '
                              'sys.stderr.write("diagnostic"); sys.exit(7)'], input=b'payload', timeout=5)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (7, b'payload', b'diagnostic'))
        with patch('probe_lsp_workload.subprocess.Popen', side_effect=OSError('launch failed')), \
             patch('probe_lsp_workload.os.killpg') as signal_group:
            with self.assertRaisesRegex(OSError, 'launch failed'):
                run_process(['not-started'], timeout=1)
            signal_group.assert_not_called()

    def test_checked_and_observation_use_same_scope(self):
        result = subprocess.CompletedProcess(['unused'], 0, b'result', b'')
        with patch('probe_lsp_workload.run_process', return_value=result) as scoped:
            self.assertEqual(checked(['compiler-or-measure'], timeout=3), b'result')
            scoped.assert_called_once_with(['compiler-or-measure'], timeout=3)
            scoped.reset_mock()
            self.assertEqual(observation(['runner'], b'input', 4), (0, b'result', '', None))
            scoped.assert_called_once_with(['runner'], input=b'input', timeout=4)


if __name__ == '__main__':
    unittest.main()
