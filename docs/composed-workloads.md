# Composed workload measurements

## Use cases

Use this offline probe to identify checking/runtime bottlenecks after shared
checked globals. It measures real composed entries and small synthetic programs
against an unchanged compiler and its existing budgets. It does not implement an
LSP server or email service. For core-operation comparisons, use the
[reference microbenchmarks](benchmarks.md); for correctness, run the test suites.

```sh
make composed-bench
# Short smoke run after make build:
python3 tools/probe_composed.py --smoke --samples 1 \
  --output build/benchmarks/composed-smoke.json
# Preserve a named report:
python3 tools/probe_composed.py --samples 3 \
  --output build/benchmarks/composed-shared.json
```

Requires the pinned Pack collection, a built compiler, Python, a C11 compiler,
and macOS or Linux with `/usr/bin/time` (`-l` on macOS, GNU `-v` on Linux).
The observer installs Fibril into `build/composed-prefix`, never a shared package
prefix. Run in a quiet, isolated checkout; concurrent builds or source edits
invalidate attribution to one compiler snapshot. OS restrictions may deny RSS
collection; that is a measurement error, not zero memory usage.

## Workloads and boundaries

- Full eight-state/eight-event email model: checking, hosted and native output.
- Global inventories: 16..512 independent definitions; only the first is
  referenced by `main`. Ordinary modules contain at most 32 globals. All loaded
  declarations are checked; only reachable declarations count toward native
  graph admission. This separates inventory checking from entry runtime work.
- Reference chains: 8..256 levels, each storing two references but selecting
  one. Modules preserve ordinary import and declaration limits.
- Recomputed Boolean globals: 4..16 levels, each demanding its predecessor
  twice. This distinguishes shared syntax from cached values.
- Single-module 63/64-global boundary, plus `main`: records the existing
  declaration threshold without changing it.
- `FullIdFour`, `EchoThenTyped`, `JSONThenTyped`, `EchoJSONThenTyped`: existing
  **admission-only** fixtures. Emission does not make their independent
  operations a wire protocol pipeline; the probe does not execute them.
- Existing Read65 JSON diagnostic: strings of 2/16/32/48/64/65 bytes and the
  dense 64-byte token array. Full buffer plus EOF, not live interactive input.
  Its independent token oracle is not a JSON-RPC decoder.
- Canonical frame echo: 2/64/256/1024/4096-byte bodies, with exact frame output
  comparison on successful runs. Echoing is not parsing the body's JSON.

## Measurement contract

Reports use schema `fibril-composed-shared-v1` and the explicit
`reachable-shared-graph` representation. They record revision, dirty status,
compiler launcher/image hashes, source hashes, toolchain/platform metadata,
raw samples and medians. `complete: false` marks an unfinished checkpoint.
Generated multi-module sources have per-module hashes. Historic expanded-tree
reports remain separate and are not rewritten.

Each sample is a fresh process with no warmup. Checking and hosted CLI execution
include startup; hosted execution includes checking. Native timing excludes C
compilation. Wall time includes the wrapper and bounded process cleanup; the
process observer polls at 10 ms. Tiny native samples are dominated by startup
and measurement overhead and cannot support throughput claims.

Peak RSS is the individual command's OS maximum resident set size in bytes,
collected by `/usr/bin/time`, not a cumulative `RUSAGE_CHILDREN` high-water mark.
It includes more than the native arena. Separate counters report peak and final
requested live arena payload, cumulative successful allocations by caller,
evaluation steps, peak depth and global calls. Payload excludes allocator
headers/overhead, stack, executable data and session buffers. Global calls count
attempted entries, including a final refused entry on exhaustion.

Native counters are inserted only into temporary runtime copies. They add no
forcing, reductions, budget charges, cache or admission exception. Plain
executables provide timing/RSS samples. Each instrumented run must match their
exit status, stdout and remaining diagnostics exactly. Successful outputs are
also checked against explicit expectations or the independent JSON token oracle.
Timeouts remain failures with unknown RSS; rejected programs remain rejected.
No timing threshold is enforced by tests. These counters are not ownership proofs.

## Local findings

These rows describe the original shared-global baseline. The later
[variable-forwarding profile and optimization](native-variable-forwarding.md)
reduce JSON evaluator work/allocation with unchanged limits; those measurements
are recorded separately.

Measured 2026-11-07 on macOS 27.2 arm64, Idris 2 `0.8.0-74b33730b`, Apple clang
21.0.0, at compiler revision `e7a7d35`. The measurement tools/docs were dirty;
compiler/runtime source matched that revision. Three fresh samples per timed
operation, with no warmup. The completed local report is
`build/benchmarks/composed-shared.json`, SHA-256
`afff714663fc3b0d259b402126c8ea3d8f9163f5bcbe1fcaddfbdce0d4fa9844`.
It contains 28 entry observations, including explicit refusals, not 28 successful
applications. The final provenance check verified unchanged source and compiler
image hashes across the matrix. Build artifacts/raw reports remain untracked.

| Executed entry/case | Shared nodes | Check median, ms | Native steps | Peak arena payload, bytes | Native median RSS, bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Full email model | 1224 | 84.2 | 1158 | 48192 | 2015232 |
| Read65, 64-byte string | 7121 | 129.6 | 55258 | 2050932 | 4816896 |
| Read65, dense 64-byte token array | 7121 | 129.6 | 97366 | 3176281 | 6422528 |
| Canonical frame, 4096-byte body | 4337 | 97.6 | 19667 | 570225 | 2768896 |

All successful native outputs matched their oracles and plain/instrumented
executions agreed. The email hosted output also matched. Native wall medians
were approximately 12..15 ms, including the 10 ms polling observer and process
startup: these are not useful execution-throughput measurements. Compiler check
RSS medians were roughly 62..67 million bytes, distinct from native arena usage.
This is a local exploratory run, not a cross-machine regression baseline.

### Admission and failure thresholds

| Probe | Observation |
| --- | --- |
| `FullIdFour` | Check/emission accepted: 2178 shared nodes, check median 103.4 ms. Admission only; no wire handshake claimed. |
| `EchoThenTyped` | Check/emission accepted: 6249 shared nodes, check median 119.8 ms. Independent fixed typed event, not frame-body routing. |
| `JSONThenTyped` | Refused at the unchanged 200000-unit construction budget, before a closed checked entry was available. |
| `EchoJSONThenTyped` | Same construction-budget refusal, during its imported lifecycle module. No runtime measurement. |
| Single-module inventory | 63 globals plus `main` accepted; 64 globals plus `main` refused at declaration parsing. |
| Multi-module inventory | 16/64/128/256/512 independent globals accepted. Reachable entry graph stays 49 nodes; all inventory declarations still checked. |
| Selected-branch reference chain | Native level 253 succeeds at depth 511; level 254 refuses at depth 512, despite only 1319 shared nodes. |
| Default hosted chain | Level 32 succeeds; sampled levels 64 and above exhaust planning reduction fuel. Hosted CLI defaults differ from native runtime policies. |
| Recomputed Boolean globals | Native level 14 uses 65551 steps; level 15 exhausts 100000 steps with a 160-node graph. Level 16 also refuses. |
| Read65, 65-byte string | Returns the diagnostic's invalid marker, as expected beyond its 64-byte parser cap; not successful larger JSON decoding. |

Inventory check medians were 96.1/83.5/83.8/84.3/91.9 ms respectively. These noisy,
startup-inclusive samples do not establish a quadratic lookup bottleneck or a
compiler speedup. All five inventory native runs use the same 17 steps and 744
payload bytes because only the first definition is reachable.

### What to optimize next

The dense 64-byte JSON case consumes 97.4% of the current native step budget.
Its final arena payload equals its peak: the workload retains its allocations
until execution ends. Immediate allocator callers account for:

| Allocation site | Count | Requested payload bytes |
| --- | ---: | ---: |
| `thunk` | 25011 | 1800792 |
| `new_value` | 29864 | 955648 |
| `extend` (environment cells) | 25856 | 413696 |
| `f_bytes_append` | 158 | 5988 |

Thunks, values and environment cells account for 99.8% of arena payload. Byte
append copies account for about 0.19%. These are direct allocation-site counts,
not inclusive call costs or proof that objects can safely be freed sooner.

The next runtime investigation should profile evaluator dispatch and
closure/environment creation in this JSON workload, then prototype reduced
allocation or shorter safe retention while preserving laziness, exact usage,
region ownership and failure behavior. Raising the arena or byte-copy budgets
does not address the first observed limit here. The existing 4096-byte canonical
framer succeeds independently; JSON decoding and composition remain blockers.

Separately, audit the construction reservations that block JSON-plus-typed
composition. No accepted closed graph exists for those refused entries, so this
report cannot assert that they would fit native admission. Tightening a
conservative estimate needs its own bound/correctness evidence.

Global-result caching and iterative/trampolined global entry may address the
synthetic recomputation and depth limits, but neither is implemented here.
Caching needs an explicit lifetime/effect contract; syntax sharing alone does
not grant one. Checking times cannot distinguish lookup, admission,
normalization, parsing and startup costs; further profiling is needed before
attributing a checker hotspot.

## Validation

The completed matrix passed its output/oracle, plain-versus-instrumented and
source/image provenance checks. `make test`, `make examples` and `make docs`
passed in the isolated worktree. The five new harness tests also passed with
ASan/UBSan enabled, including a separately labelled trusted-C depth-exhaustion
probe. These validate measurement behavior, not production capacity or safety.
