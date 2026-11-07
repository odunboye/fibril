#!/usr/bin/env python3
"""OFFLINE corpus/evidence checks; recorded cap denials are not parser passes."""
from contextlib import contextmanager
import errno
import hashlib
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

from generate_lsp_workload import (DESTINATION, ROOT, SOURCE, ObjectMembers, artifacts,
                                   bodies, describe, frame)
from observe_json_state_sharing import oracle
from probe_lsp_workload import ProbeProcessCleanupError, checked, observation, run_process
from lsp_evidence_history import verify_workload_evidence


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
        evidence = verify_workload_evidence(ROOT / 'docs/assets/evidence/lsp-workload.json')
        self.assertEqual(evidence['corpus_manifest_sha256'], hashlib.sha256(artifacts()['manifest.json']).hexdigest())
        self.assertEqual(len(evidence['production_source_sha256']), 8)
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
        normal = verify_workload_evidence(ROOT / 'docs/assets/evidence/lsp-workload.json')
        sanitized = verify_workload_evidence(ROOT / 'docs/assets/evidence/lsp-workload-sanitized.json')
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
sys.stdout.write('tree-output'); sys.stdout.flush()
sys.stderr.write('tree-error'); sys.stderr.flush()
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
        real_popen, real_killpg, real_waitid = subprocess.Popen, os.killpg, os.waitid
        processes, files, connections, ordering = [], [], [], []
        handshake_done = False
        with tempfile.TemporaryDirectory(prefix='lsp-probe-process-', dir='/tmp') as temporary:
            # macOS Unix sockets have a short path limit; /tmp avoids long TMPDIR.
            path = str(Path(temporary) / 'ready.sock')
            with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
                listener.settimeout(5)
                listener.bind(path)
                listener.listen(1)

                def launch(*args, **kwargs):
                    self.assertTrue(kwargs['start_new_session'])
                    files.extend(kwargs[key] for key in ('stdin', 'stdout', 'stderr'))
                    process = real_popen(*args, **kwargs)
                    processes.append(process)
                    reap = process.wait

                    def only_after_final_signal(**options):
                        self.assertEqual(ordering[-1], signal.SIGKILL)
                        ordering.append('reap')
                        return reap(**options)

                    process.wait = only_after_final_signal
                    process.poll = lambda: self.fail('poll would reap before final signaling')
                    process.communicate = lambda **_: self.fail('communicate would reap before final signaling')
                    return process

                def nonreaping(kind, pid, flags):
                    nonlocal handshake_done
                    self.assertEqual((kind, pid), (os.P_PID, processes[0].pid))
                    self.assertEqual(flags, os.WEXITED | os.WNOWAIT | os.WNOHANG)
                    if not handshake_done:
                        connection, _ = listener.accept()
                        connections.append(connection)
                        connection.settimeout(5)
                        with connection.makefile('rb') as stream:
                            ready = json.loads(stream.readline(1024))
                        self.assertNotEqual(ready['pid'], pid)
                        self.assertEqual(ready['group'], pid)
                        handshake_done = True
                        if cancellation is not None:
                            raise cancellation
                    state = real_waitid(kind, pid, flags)
                    ordering.append('exited-unreaped' if state is not None else 'running-unreaped')
                    return state

                def signal_owned(group, signum):
                    self.assertEqual(group, processes[0].pid)
                    self.assertNotEqual(group, os.getpgrp())
                    self.assertIsNone(processes[0].returncode)
                    # This syscall would raise ECHILD if the anchor was reaped;
                    # observing WNOWAIT again does not release its PID/group id.
                    state = real_waitid(os.P_PID, group, os.WEXITED | os.WNOWAIT | os.WNOHANG)
                    if exited_leader:
                        self.assertIsNotNone(state)
                        if signum == signal.SIGKILL:
                            # Its socket is still live AFTER TERM and leader
                            # exit; only the following group KILL may close it.
                            connections[0].setblocking(False)
                            try:
                                with self.assertRaises(BlockingIOError):
                                    connections[0].recv(1)
                            finally:
                                connections[0].settimeout(5)
                    self.assertNotIn('reap', ordering)
                    ordering.append(signum)
                    real_killpg(group, signum)

                command = [sys.executable, '-c', PROCESS_TREE, path, 'exit' if exited_leader else 'wait']
                cleanup_verified = False
                try:
                    with patch('probe_lsp_workload.subprocess.Popen', side_effect=launch), \
                         patch('probe_lsp_workload.os.waitid', side_effect=nonreaping), \
                         patch('probe_lsp_workload.os.killpg', side_effect=signal_owned):
                        if cancellation is not None:
                            with self.assertRaises(type(cancellation)) as raised:
                                run_process(command, timeout=0.05)
                            self.assertIs(raised.exception, cancellation)
                        elif exited_leader:
                            result = run_process(command, timeout=1)
                            self.assertEqual((result.returncode, result.stdout, result.stderr),
                                             (0, b'tree-output', b'tree-error'))
                        else:
                            with self.assertRaises(subprocess.TimeoutExpired) as raised:
                                run_process(command, timeout=0.05)
                            self.assertEqual((raised.exception.output, raised.exception.stderr),
                                             (b'tree-output', b'tree-error'))
                    self.assertEqual([entry for entry in ordering if isinstance(entry, signal.Signals)],
                                     [signal.SIGTERM, signal.SIGKILL])
                    self.assertEqual(ordering[-2:], [signal.SIGKILL, 'reap'])
                    self.assertEqual(connections[0].recv(1), b'')
                    self.assertEqual(processes[0].returncode, 0 if exited_leader else -signal.SIGKILL)
                    cleanup_verified = True
                    self.assertTrue(all(stream.closed for stream in files))
                finally:
                    # Never signal a group after the helper already reaped its
                    # leader, even when an assertion fails after that point.
                    for process in processes:
                        if not cleanup_verified and process.returncode is None:
                            try:
                                real_waitid(os.P_PID, process.pid, os.WEXITED | os.WNOWAIT | os.WNOHANG)
                            except ChildProcessError:
                                pass  # Ownership lost: do not signal this number.
                            else:
                                try:
                                    real_killpg(process.pid, signal.SIGKILL)
                                except ProcessLookupError:
                                    pass
                                subprocess.Popen.wait(process, timeout=2)
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
        # Real exited anchors without descendants exercise macOS's EPERM case.
        for status in (0, 7):
            with self.subTest(status=status):
                result = run_process([sys.executable, '-c',
                                      'import sys; sys.stdout.buffer.write(sys.stdin.buffer.read()); '
                                      f'sys.stderr.write("diagnostic"); sys.exit({status})'],
                                     input=b'payload', timeout=5)
                self.assertEqual((result.returncode, result.stdout, result.stderr),
                                 (status, b'payload', b'diagnostic'))
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


    @contextmanager
    def controlled_anchor(self, *, observations=(), running=False, platform='darwin',
                          signal_error=None, reap_error=None):
        """No real process: expose ordering/error paths without leaking a child."""
        process = Mock(pid=1234567, returncode=None)
        events = []
        states = iter(observations)
        ready = None if running else SimpleNamespace(si_pid=process.pid)

        def observe(kind, pid, flags):
            self.assertEqual((kind, pid, flags),
                             (os.P_PID, process.pid, os.WEXITED | os.WNOWAIT | os.WNOHANG))
            events.append('observe')
            state = next(states, ready)
            if isinstance(state, BaseException):
                raise state
            return state

        def signal_owned(pid, signum):
            self.assertEqual(pid, process.pid)
            self.assertEqual(events[-1], 'observe')
            self.assertIsNone(process.returncode)
            events.append(signum)
            if signal_error is not None:
                raise signal_error

        def reap(*, timeout):
            self.assertEqual(events[-1], signal.SIGKILL)
            self.assertEqual(timeout, 2)
            events.append('reap')
            if reap_error is not None:
                raise reap_error
            process.returncode = 0
            return 0

        process.wait.side_effect = reap
        process.poll.side_effect = AssertionError('poll would release the anchor')
        process.communicate.side_effect = AssertionError('communicate would release the anchor')
        with patch('probe_lsp_workload.subprocess.Popen', return_value=process), \
             patch('probe_lsp_workload.os.waitid', side_effect=observe), \
             patch('probe_lsp_workload.os.killpg', side_effect=signal_owned), \
             patch('probe_lsp_workload.sys.platform', platform):
            yield process, events

    def test_cleanup_order_keeps_anchor_until_final_signal(self):
        with self.controlled_anchor() as (process, events):
            self.assertEqual(run_process(['fake'], timeout=1).returncode, 0)
            self.assertEqual(events, ['observe', 'observe', signal.SIGTERM, 'observe',
                                      'observe', signal.SIGKILL, 'reap'])
            process.poll.assert_not_called()
            process.communicate.assert_not_called()

    def test_unsupported_platform_and_sigchld_fail_before_launch(self):
        for missing in ('waitid', 'WNOWAIT', 'WNOHANG'):
            with self.subTest(missing=missing), \
                 patch('probe_lsp_workload.os.' + missing, None), \
                 patch('probe_lsp_workload.subprocess.Popen') as launch:
                with self.assertRaisesRegex(RuntimeError, 'requires POSIX waitid'):
                    run_process(['not-started'])
                launch.assert_not_called()
        with patch('probe_lsp_workload.os.name', 'nt'), \
             patch('probe_lsp_workload.subprocess.Popen') as launch:
            with self.assertRaisesRegex(RuntimeError, 'requires POSIX waitid'):
                run_process(['not-started'])
            launch.assert_not_called()
        for handler in (signal.SIG_IGN, lambda *_: None):
            with self.subTest(handler=handler), \
                 patch('probe_lsp_workload.signal.getsignal', return_value=handler), \
                 patch('probe_lsp_workload.subprocess.Popen') as launch:
                with self.assertRaisesRegex(RuntimeError, 'requires default SIGCHLD'):
                    run_process(['not-started'])
                launch.assert_not_called()

    def test_macos_exited_anchor_signal_refusal_still_precedes_reap(self):
        with self.controlled_anchor(signal_error=PermissionError(errno.EPERM, 'refused')) as (process, events):
            self.assertEqual(run_process(['fake'], timeout=1).returncode, 0)
            self.assertEqual([event for event in events if event != 'observe'],
                             [signal.SIGTERM, signal.SIGKILL, 'reap'])
            process.wait.assert_called_once_with(timeout=2)

    def test_other_signal_errors_fail_closed(self):
        for options, failure in [
            ({'running': True}, PermissionError(errno.EPERM, 'running anchor refused')),
            ({'platform': 'linux'}, PermissionError(errno.EPERM, 'non-mac refused')),
            ({}, OSError(errno.EIO, 'other failure')),
            ({}, PermissionError(errno.EACCES, 'not EPERM')),
        ]:
            with self.subTest(options=options, failure=failure), \
                 self.controlled_anchor(signal_error=failure, **options):
                with self.assertRaises(type(failure)) as raised:
                    run_process(['fake'], timeout=0)
                self.assertIs(raised.exception, failure)

    def test_lost_anchor_stops_further_numeric_group_signals(self):
        ready = SimpleNamespace(si_pid=1234567)
        for states, expected_signals in [
            ([ChildProcessError()], []),
            ([ready, ready, ChildProcessError()], [signal.SIGTERM]),
            ([ready, ready, ready, ChildProcessError()], [signal.SIGTERM]),
        ]:
            with self.subTest(states=states), \
                 self.controlled_anchor(observations=states,
                                        signal_error=PermissionError(errno.EPERM, 'mac refusal')) as (process, events):
                with self.assertRaisesRegex(ProbeProcessCleanupError, 'anchor lost'):
                    run_process(['fake'], timeout=1)
                self.assertEqual([entry for entry in events if isinstance(entry, signal.Signals)], expected_signals)
                process.wait.assert_not_called()

    def test_interrupted_nonreaping_observations_keep_deadline(self):
        for timeout, expected_timeout in ((0.5, True), (5, False)):
            with self.subTest(timeout=timeout), \
                 self.controlled_anchor(observations=[InterruptedError()]), \
                 patch('probe_lsp_workload.time.monotonic', side_effect=range(100)), \
                 patch('probe_lsp_workload.threading.Event') as event:
                if expected_timeout:
                    with self.assertRaises(subprocess.TimeoutExpired):
                        run_process(['fake'], timeout=timeout)
                else:
                    self.assertEqual(run_process(['fake'], timeout=timeout).returncode, 0)
                for invocation in event.return_value.wait.call_args_list:
                    self.assertLessEqual(invocation.args[0], 0.01)

    def test_final_reap_deadline_is_cleanup_failure_not_success(self):
        with self.controlled_anchor(reap_error=subprocess.TimeoutExpired('fake', 2)):
            with self.assertRaisesRegex(ProbeProcessCleanupError, 'cleanup failed'):
                run_process(['fake'], timeout=1)


if __name__ == '__main__':
    unittest.main()
