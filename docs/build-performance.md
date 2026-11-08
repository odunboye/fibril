# Build performance

Investigation and implementation: 2026-11-08, Fibril source revision `c8caac2`.
The Fibril implementation and its `%default total` directives are unchanged.

## Result

`make build` now uses a guarded, worktree-local Idris adapter that avoids eagerly
allocating termination-error call paths. It retains the pinned compiler API,
size-change algorithm, termination decisions and error diagnostics. The installed
compiler and `pack.toml` collection pin are unchanged.

Measurements on the same 24 GiB, 14-logical-CPU macOS machine:

| Build scenario | Wall time | Fibril modules rebuilt |
| --- | ---: | ---: |
| Stock pinned compiler, empty Fibril cache | 38 min 57.8 s | 160 |
| Local adapter, empty adapter and Fibril caches | 2 min 2.5 s | 160 |
| Local adapter already cached, empty Fibril cache | 1 min 33.1 s | 160 |
| Unchanged executable rebuild | 7.76 s | 0 |
| Unchanged typecheck only | 2.29 s | 0 |

The first adapter row includes its one-time bootstrap. A new machine still needs
Pack, the pinned compiler/API library, dependencies and Chez installed. These are
single observations, not timing guarantees or CI thresholds. Exploratory compiler
runs overlapped early in the stock baseline and caused contention; therefore its
wall time is contextual rather than a controlled comparative measurement. The
per-module process-CPU timings give much stronger attribution:

| Expression module phase | Stock | Local adapter (cached-host clean build) |
| --- | ---: | ---: |
| Processing declarations | 1.440 CPU s | 1.207 CPU s |
| Totality checking | 1,996.071 CPU s | 4.988 CPU s |
| Whole module elaboration | 1,997.825 CPU s | 6.485 CPU s |

The cold adapter build recorded approximately 0.83 GiB maximum child RSS; the
stock compiler was sampled at roughly 8–9 GiB resident memory during its long
check. The stock run did not record a complete peak-RSS measurement. The separate
independent review records a short GC-heavy native sample; that sample must not
be interpreted as a whole-build GC percentage.

## Cause and fix

The host compiler's `Core.Termination.SizeChange` represents each graph using:

- an argument-change matrix, used to decide termination;
- a list of calls along the path, used for diagnostics.

Its `composeGraph` concatenates the diagnostic lists eagerly while computing
closure. Equality and ordering of graphs compare their matrices, not these lists.
Consequently a successful check can spend substantial time and memory building
call paths that are never displayed. The elaborator's large recursive component
makes this particularly expensive.

The adapter changes only that diagnostic representation to `Lazy CallSeq`,
constructs concatenations with `Delay`, and forces the list when rendering a graph
or reporting a failing recursive path. Matrix construction, multiplication,
worklist ordering, closure, loop detection and totality policies are unchanged.
There are no new unchecked totality assertions, partiality directives, or fuel
limits. Diagnostic list contents are preserved when forced.

The installed API source is guarded by both compiler revision
`74b33730b6fea649b15e8d01ab099df9effcc7a0` and SHA256
`19e955759d52f9ae4c6691809941032fa050d667e5ae47be92c1e1429517040d`.
`tools/fibril_idris.py` contains the small, exact source transformation. It builds
only the modified module and a normal `Idris.Driver.mainWithCodegens []` entry
point against that pinned API. Generated source, executable and an identity
manifest live under `build/host-compiler/<key>/`. A file lock prevents concurrent
bootstrap races. No global compiler files or installed packages are patched.

`make build` continues to install Fibril's dependencies through Pack, then calls
this adapter. The wrapper preserves caller-selected `IDRIS2_PREFIX`, package,
library and support-data paths. This is important for `tools/test_units.py`'s
private test installation; the generated global Pack shim can overwrite those
paths. The test runner now defaults to the local wrapper as well.

## Validation

All **160 compiled `.ttc` interfaces are byte-for-byte identical** between the
stock clean baseline and the cold adapter build. The comparison is recorded in
`build/build-audit/checked-interface-comparison.json`. No source refactor in
`src/Fibril` was retained.

`make host-compiler-test` checks:

- acceptance of structural recursion, mutually recursive argument swapping, and
  recursion through a local helper;
- rejection of direct, mutual and local nondecreasing loops;
- identical stock/adapter exit status and diagnostics, including failing paths;
- byte-identical checked interfaces for accepted fixtures;
- preservation of a caller's private prefix and package path;
- rejection of an unrecognized compiler source before applying the patch.

Validation passed: the host-compiler comparisons, `make unit-test`, all 190 CLI
tests, all 27 pattern-clause tests, the runnable examples, and all 16 handbook
tests (including generated local-file link checks). Example and handbook targets
used their already validated build/unit prerequisites rather than rerunning them.

## Reproducing the measurements

Normal builds and checker agreement tests:

```sh
make build
make unit-test
make host-compiler-test
```

To use the original compiler, use `make IDRIS2=idris2 build` or `pack build fibril`.
Those commands can reuse already checked interfaces. For an independent stock
recheck, use a fresh profiler cache:

```sh
python3 tools/profile_build.py --cache build/build-profiles/stock-check/cache --timing 3
python3 tools/profile_build.py --compiler tools/fibril_idris.py --cache build/build-profiles/local-check/cache --timing 3
```

Repeat the second command with the same cache for an unchanged rebuild. Add
`--typecheck` to omit executable generation. `make clean` also removes the private
adapter, so its next use includes bootstrap again.

Each profiler invocation writes `compiler.log` and `summary.json` under a new
`build/build-profiles/` timestamp directory. The summary records the compiler,
source-input digest, source-tree dirty state, cached/rebuilt module counts, wall
time, child CPU times, maximum recorded child RSS, module CPU timings and the
slowest completed termination checks. Compiler timing entries use process CPU
time, exclude subprocess CPU time, and overlap when nested; do not sum every
entry or equate them with wall time. The outer wall clock includes subprocesses.

The recorded runs are:

| Scenario | Summary directory under `build/build-profiles/` |
| --- | --- |
| Stock baseline | `20261108T164152928373Z` |
| Cold adapter | `20261108T175229520756Z` |
| Cached adapter, clean Fibril | `20261108T175526480151Z` |
| Unchanged executable | `20261108T175725099255Z` |
| Unchanged typecheck | `20261108T175734474163Z` |

The optimized source-input digest is
`2898085a73f95001f631f4b572353614ae4759d9420eddfb7cf0cb0e3f0b631a`.
Raw artifacts are intentionally ignored build outputs and are removed by clean.
The older stock profiler summary lacks the later CPU/RSS/source-digest fields.

## Remaining work and maintenance

The adapter deliberately refuses unknown compiler revisions or source hashes.
Review the small transformation and rerun agreement/regression tests when
upgrading the pinned collection. Until this optimization is available in the
selected upstream compiler, the stock override remains available.

`Cubical.Logical.ShadowCommon` is now the largest measured module at about
37 CPU seconds. Repeated executable generation still accounts for much of an
unchanged build. Library/CLI package separation or incremental Chez could address
that separately; neither is needed for the large improvement above. Removing the
26 modules outside Main's import closure saved only about 5.6 CPU seconds in the
initial investigation, and `make -j` cannot parallelize one host termination check.

The earlier bundling, inlining and typed-local-binding source experiments were
not retained. Some were stopped incomplete; the binding trial's first check was
about 23% faster, but that is not evidence for its whole-module performance. The
successful host optimization avoids coupling Fibril's source structure to this
compiler allocation problem.
