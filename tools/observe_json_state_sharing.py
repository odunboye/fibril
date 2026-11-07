#!/usr/bin/env python3
"""Bounded hosted observations of the shared JSON diagnostic, not a library test.

No fuel/budget changes. Exit zero means observations completed, NOT that blocked
cases passed. JSON grammar acceptance comes from Python; raw lexeme tokenization
is independent of the Fibril state machine. Escaped lone surrogates are reported
separately because Python accepts them but the prototype requires scalar Unicode.
"""
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tools/fixtures/json-admission'
TOKEN = re.compile(rb'\s+|[{}\[\]:,]|"(?:[^"\\]|\\.)*"|-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?|true|false|null')


def check_source_preservation():
    original = (FIXTURES / 'full/Protocol/JSON.fib').read_text()
    body = original.split('parseJSON input = ', 1)[1]
    abstract = body.replace('Scan', 'S').replace('Sning', 'scanning')
    abstract = abstract.replace('consumeS (\\(0 self : S) => S)', 'eliminate S')
    abstract = abstract.replace('consumeS (\\(0 self : S) => JSONResult)', 'eliminate JSONResult')
    for variant in ['factored', 'shared']:
        source = (FIXTURES / variant / 'Protocol/JSON.fib').read_text()
        actual = source.split('parseJSONKernel S scanning eliminate input = ', 1)[1]
        actual = actual.split('\n-- Instantiate the abstract kernel once;', 1)[0]
        expected = abstract
        if variant == 'shared':
            expected = expected.replace('equalString', 'sameText')
            expected = expected.replace('case primBytesShare input of Shared original =>\n',
                'case primBytesShare input of Shared original =>\n'
                '  let (sameText : (1 left : String) -> (1 right : String) -> Bool) = equalString in\n', 1)
        assert actual == expected, f'{variant}: grammar/state/token body changed'
        for entry in ['Parse.fib', 'Main.fib']:
            assert (FIXTURES / variant / entry).read_bytes() == (FIXTURES / 'full' / entry).read_bytes()


def reject_constant(value):
    raise ValueError(value)


def scalar_unicode(value):
    if isinstance(value, str):
        value.encode('utf-8', errors='strict')
    elif isinstance(value, list):
        for item in value:
            scalar_unicode(item)
    elif isinstance(value, dict):
        for key, item in value.items():
            scalar_unicode(key)
            scalar_unicode(item)


def oracle(data):
    try:
        value = json.loads(data.decode('utf-8', errors='strict'), parse_constant=reject_constant)
    except (ValueError, UnicodeError):
        return False, False, b'\0'
    try:
        scalar_unicode(value)
    except UnicodeError:
        return True, False, b'\0'
    if len(data) > 64:
        return True, True, b'\0'
    output = bytearray()
    position = 0
    depth = 0
    maximum_depth = 0
    for match in TOKEN.finditer(data):
        assert match.start() == position, 'oracle tokenization gap'
        position = match.end()
        token = match.group()
        if token.isspace():
            continue
        if token[:1] == b'"':
            output.extend(b'S' + token + b'\0')
        elif token == b'true':
            output.extend(b'T')
        elif token == b'false':
            output.extend(b'F')
        elif token == b'null':
            output.extend(b'N')
        elif token[:1] in b'-0123456789':
            output.extend(b'#' + token + b'\0')
        else:
            output.extend(token)
            if token in [b'[', b'{']:
                depth += 1
                maximum_depth = max(maximum_depth, depth)
            elif token in [b']', b'}']:
                depth -= 1
    assert position == len(data), 'oracle tokenization incomplete'
    return True, True, b'\0' if maximum_depth > 8 else bytes(output)


def cases():
    fixed = [b'', b' ', b'0', b'1', b'-1', b'1.0', b'1e2', b'true', b'false', b'null',
             b'[]', b'{}', b'[ ]', b'[1]', b'[1,2]', b'{"a":1}', b'{"a":1,"a":2}',
             b'""', b'"a"', b'"\\n"', b'"\\u0041"', b'"\\uD834\\uDD1E"',
             '"é"'.encode(), '"𝄞"'.encode(), b'"\\ud800"', b'"\\udc00"',
             b'"\\uD800\\u0041"', b'"\\x"', b'"\x01"', b'"\xff"', b'"\xc0\x80"',
             b'"\xed\xa0\x80"', b'01', b'-', b'1.', b'1e', b'1e+', b'+1', b'.1',
             b'True', b'NaN', b'nullx', b'true false', b'[]x', b'[1,]', b'{"a":}',
             b'{a:1}', b'{"a" 1}', b'[,]', b'[}', b'{}{}']
    for index, data in enumerate(fixed):
        yield f'grammar-{index}', data
    # Probe short length families and source boundaries explicitly.
    # No global runtime cap is inferred from these grammar-dependent results.
    for name, lengths, make in [
        ('number-length', range(1, 9), lambda n: b'1' * n),
        ('string-length', range(2, 14), lambda n: b'"' + b'a' * (n - 2) + b'"'),
        ('input-bytes', [63, 64, 65], lambda n: b' ' * (n - 1) + b'1'),
        ('depth', [1, 2, 8, 9], lambda n: b'[' * n + b']' * n),
        ('token-count', [2, 3, 5, 63], lambda n: b'[]' if n == 2 else b'[' + b','.join([b'0'] * ((n - 1) // 2)) + b']'),
        ('short-product', range(12), lambda n: [b' ', b'\t', b'\n'][n // 4] + [b'0', b'[]', b'{}', b'null'][n % 4]),
    ]:
        for n in lengths:
            yield f'{name}-{n}', make(n)


def main():
    check_source_preservation()
    print(json.dumps({'source_preservation': 'passed'}), flush=True)
    source = FIXTURES / 'shared'
    exe = os.environ.get('FIBRIL', str(ROOT / 'build/exec/fibril'))
    command = [exe, 'run-binary', '--source-dir', str(source), str(source / 'Read65.fib')]
    counts = {'executed_matches': 0, 'runtime_blocked': 0, 'wrapper_eof': 0,
              'mismatches': 0, 'unexpected_failures': 0}
    for label, data in cases():
        python_accepts, scalar_policy_accepts, expected = oracle(data)
        start = time.monotonic()
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True, cwd=ROOT)
        try:
            out, err = process.communicate(data, timeout=15)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        if process.returncode == 0:
            category = 'executed_matches' if out == expected and not err else 'mismatches'
        elif process.returncode == 1 and err == b'Binary reduction budget exhausted\n' and not out:
            category = 'runtime_blocked'
        elif not data and process.returncode == 1 and err == b'Binary program rejected input\n' and not out:
            # primReadBytes reports EOF; this does not execute the empty parser.
            category = 'wrapper_eof'
        else:
            category = 'unexpected_failures'
        counts[category] += 1
        print(json.dumps({'case': label, 'input_hex': data.hex(), 'input_bytes': len(data),
                          'python_accepts': python_accepts,
                          'scalar_policy_accepts': scalar_policy_accepts,
                          'expected_hex': expected.hex(), 'status': process.returncode,
                          'stdout_hex': out.hex(), 'stderr': err.decode(errors='replace'),
                          'seconds': round(time.monotonic() - start, 4), 'category': category}), flush=True)
    print(json.dumps({'summary': counts, 'validation': 'blocked' if counts['runtime_blocked'] else 'completed'}))
    if counts['mismatches'] or counts['unexpected_failures']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
