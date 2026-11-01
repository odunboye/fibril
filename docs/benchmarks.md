# Reference benchmark suite

Status: implemented exploratory measurement, not a stable performance guarantee.

## Run

```sh
make bench-smoke
make bench
```

Both build the separate pack project in bench/ using the Chez code generator.
Smoke mode uses size 2, one sample, one warmup process, one iteration.
The exploratory suite uses sizes 2/4/6, five samples, one warmup process, and
ten iterations per sample. Reports go to build/benchmarks/latest.json (ignored).

Each run replaces latest.json; preserve named reports with:

```sh
python3 tools/benchmark.py --output build/benchmarks/before.json
```

## Workloads

[Workloads](../bench/src/Workloads.idr) constructs inputs, performs the operation,
and validates its result within the timed batch.

| Workload | Input and validated operation |
| --- | --- |
| substitution | Open application spine; substitute a closed universe expression |
| reduction | Nested identity applications; normalize within the exact beta-step budget |
| erased | Type-check nested identity applications at changing universe levels |
| runtime | Check closed polymorphic identities wrapped in linear identity applications |
| interval | Product of disjoint two-generator joins; compare against double reversal |
| face | Product of two-endpoint disjunctions; entail its first factor |
| expose-full | Fully normalize a Pi with nested codomain redexes and confirm Pi shape |
| expose-head | Expose the same Pi shape without entering its codomain |

The products produce up to 2^size DNF clauses before absorption; they deliberately
expose solver growth. Size is currently restricted to 1..6 and iteration count
to 1..1000. These caps are not a sandbox or general resource guarantee.

## What is measured

The Idris driver measures monotonic batch duration inside the process. Construction,
checking/result validation, iteration overhead, and checksum formatting/output
are included; compiler build and process startup are excluded. Each sample is a
fresh process. A warmup process does not warm the following process's heap or JIT.

Per-iteration values divide batch duration by iteration count; they are not
isolated operation timings. Very small workloads are dominated by harness/clock/
output overhead. Inputs vary by iteration seed, but compiler optimization can
still affect these microbenchmarks.

The Python runner validates checksums and records raw samples, medians, revision,
dirty-tree status, source hashes, platform information, package/compiler metadata,
and code generator. It does not measure allocations, peak RSS, GC cost, or
hard-real-time worst-case execution time.

## First exploratory observations

The initial local run showed DNF interval and face workloads growing sharply
between sizes 2 and 6. This supports investigating symbolic solver scaling.
Tiny substitution/reduction batches were near harness overhead and should not be
used to advertise checker speed. No stable cross-machine baseline or regression
threshold is established. Current reports, not prose numbers, are the measurement
record.

## First measured optimization: sorted DNF helpers

The solvers already canonicalize their literal lists. Sorted.idr now removes
duplicates by an adjacent linear scan after sorting and checks subsets with a
linear merge walk rather than repeated membership searches.

Local exploratory comparison (macOS arm64, pinned collection, Chez; five fresh
samples of ten iterations; batch medians divided by iteration count):

| Workload | Size | Before, ms/iteration | After, ms/iteration |
| --- | --- | --- | --- |
| interval | 4 | 0.1655 | 0.0443 |
| interval | 6 | 3.4392 | 0.5040 |
| face | 4 | 0.1355 | 0.0483 |
| face | 6 | 2.3256 | 0.5083 |

The before report was collected at 7dd3151; the after report records the same
parent revision with a dirty tree and changed source hashes. Reports remain at
build/benchmarks/sorted-before.json and sorted-after.json locally; they are not
portable baselines or tracked artifacts. This table preserves the observed
summary, not a claim that every workload or machine has the same improvement.

Frozen pre-optimization interval and face algorithms live in test/src/Tests/Reference.
Hedgehog compares their answers with production results. Helpers are also checked
against sorting/deduplication and membership-based subset algorithms. These
comparisons detect regressions relative to the old algorithms, not shared
semantic mistakes or all possible inputs.

The merge helper requires ascending inputs; production callers establish that
through canonicalization. This is a documented precondition, not an indexed
proof. DNF expansion and pairwise absorption remain potentially exponential.

## Maintenance and next improvements

- Tests validate report structure and reject unsupported/unbounded driver requests.
- Preserve correctness checks when changing a workload; label changed benchmark
  definitions and compare matching source/toolchain hashes.
- Increase durations, add in-process warmup/calibration and deeper term fixtures,
  and collect supported memory metrics before making strong speed claims.
- Head-only exposure workloads now exist; small sizes remain overhead-sensitive.
  Add deeper/calibrated fixtures before claiming a measured speedup. Repeated
  checking remains a candidate for investigation.
- Keep stable reference implementations as differential oracles.
- Do not add noisy timing thresholds until a repeatable environment exists.

See [safety/performance policy](safety-performance.md) and [testing](testing.md).
