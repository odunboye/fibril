#!/usr/bin/env python3
"""Compare validated 4 MiB transfers using one shared compiled test fixture.

Reports observations, never a timing assertion. Requires the same compiler as
io-binary-test. Times include process startup; build time is reported separately.
"""
import argparse
import json
import statistics
import time

from test_io_binary import BinaryTransport


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats', type=int, default=3)
    args = parser.parse_args()
    if not 1 <= args.repeats <= 7:
        parser.error('--repeats must be 1..7')
    try:
        start = time.perf_counter()
        BinaryTransport.setUpClass()
        built = time.perf_counter() - start
        case = BinaryTransport()
        data = bytes(range(256)) * 16384
        observations = []
        for label, executable, adapter in [
            ('host-reference', case.host, 'reference'),
            ('host-block', case.host, 'block'),
            ('native-reference', case.native, 'block'),
        ]:
            # Warm up loading and capture an empty-session startup observation.
            start = time.perf_counter()
            empty = case.run_mode(executable, 'empty', adapter=adapter)
            startup = time.perf_counter() - start
            if (empty.returncode, empty.stdout, empty.stderr) != (0, b'', b'ok\n'):
                raise SystemExit(f'{label} startup failed: {empty!r}')
            samples = []
            for _ in range(args.repeats):
                start = time.perf_counter()
                result = case.run_mode(executable, 'bench', data, adapter=adapter, timeout=180)
                samples.append(time.perf_counter() - start)
                if (result.returncode, result.stdout, result.stderr) != (0, data, b'ok\n'):
                    raise SystemExit(f'{label} transfer failed: status={result.returncode}, stderr={result.stderr!r}')
            median = statistics.median(samples)
            observations.append({'adapter': label, 'startup_seconds': startup,
                'samples_seconds': samples, 'median_seconds': median,
                'payload_mib_per_second': len(data) / (1024 * 1024) / median})
        print(json.dumps({'payload_bytes': len(data), 'chunk_bytes': 65536,
            'build_seconds': built, 'observations': observations}, indent=2))
    finally:
        BinaryTransport.doClassCleanups()


if __name__ == '__main__':
    main()
