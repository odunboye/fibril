# LSP status: usable Python server and Fibril-written next gate

## Bottom line

**The usable [Python LSP server](lsp.md) is now merged alongside master's current
compiler features. There is no usable wire-level LSP server written in Fibril yet.**
The Python server provides editor integration with compiler-backed checking and
navigation; its implementation and tests are unchanged from `9e87c0d`. The
Fibril-written work provides checked binary-IO foundations, canonical framing,
bounded parser/lifecycle diagnostics and historical performance evidence. Merging
them does not turn those diagnostics into production APIs or rerun historical
performance measurements on the current compiler.

The [shared checked-global representation](shared-checked-globals.md) is now
implemented for named modules and their hosted/native execution paths. This does
not rerun the historical measurements below or deliver a wire-level server;
composed workloads must be measured again under the explicit shared-graph policy.

## Implemented Fibril-written foundations

- Checked hosted/native binary IO, immutable Bytes and fallible strict UTF-8
  conversion, with separate capability gates and existing resource/work limits.
- Fibril-written canonical `Content-Length: N\r\n\r\n` framing for opaque
  **0..4096-byte bodies**. One/two-frame clients validate before output and flush
  without waiting for EOF. Alternate/general headers are not supported.
- Bounded binary iteration with explicit Done/Continue and Finished/Exhausted
  states, charged count decoding, and reviewed native pending-frame/lifetime behavior.
- A **64-byte JSON diagnostic**: pure `parseJSON` remains distinct from explicitly
  binary-effectful `parseJSONBinary`, which processes already-buffered Bytes with
  no reads/writes/flushes of its own. Both share one transition/finalizer. Tokens
  preserve raw lexemes and duplicate members; they are not a decoded JSON AST.
- A **pure typed-event lifecycle prototype** for initialize, initialized,
  shutdown and exit. It preserves opaque integer/string IDs under documented
  future-decoder preconditions. It does not decode requests, serialize responses,
  negotiate capabilities or exit a process.
- Reproducible offline reference-shaped/synthetic workloads, cost inventories,
  and candidate-only source sharing. These are not captured editor traffic.

## Measured blockers (historical pre-master-integration profiles)

| Area | Evidence and limitation |
| --- | --- |
| General headers | Best measured 1024-byte scanner exhausts native work after182 reads; long names also hit depth/fuel limits. No `withFrame` API is delivered. |
| Real JSON workload | Capability-rich initialize is3681 bytes/720 lexical tokens; even the small reference-shaped initialize is247 bytes. Read65 cap denials examine no complete larger message. |
| Runtime representation | Dense64 JSON costs97768 native steps and2998705 arena-payload bytes. Two helper aliases improve this only to95602/2894705. Most retained allocation is thunks, values/closures and environments, not copied byte buffers. |
| Initial syntax | Candidate framing falls4341→3719 nodes and JSON reader8002→6732, but echo plus fixed typed observation still needs10781 nodes, above8192. |
| Construction/composition | JSON-plus-typed attempts exhaust200000 construction units. Full-ID four-event lifecycle observation needs8467 nodes. Independent component fits are not server-composition evidence. |

No budgets or whole-syntax gates were relaxed. Counting only erased/computational
syntax, or counting unique DAG nodes instead of the existing tree, would be an
admission-policy change—not an already-approved optimization.

## Validation and evidence limits

Prior isolated foundations passed the combined `make -j8 test editor-test handbook`
gate and targeted hosted/native sanitizer checks. Lifecycle groups were executed
normally and under ASan/UBSan; all133 recorded rows match, with53 full-ID and12
control-only outputs per backend plus no-output sessions. Workload/model/audit
checks and handbook checks also passed at their documented checkpoints.

The source-sharing candidate's original thirty-minute agent run **timed out**.
Its cached logs record completed normal/sanitized JSON and framing suites before
that timeout; a bounded recovery packaged those records without rerunning them.
A later subprocess-routing correction has offline/tiny-child regression evidence,
not newly claimed matrix execution. The timeout is not retroactively a pass.
Historical compiler/source hashes describe their recorded revisions; a later
master integration must not claim those old observations were rerun on new code.
See the historical [bootstrap merge validation record](lsp-merge-validation.md)
for tests executed at that earlier merge and explicit historical-source
verification. Those results are not execution evidence for this newer integration.

## Next work for a Fibril-written server

1. Re-measure actual composed entries with shared checked globals, then prioritize
   retained-allocation work from that evidence while preserving whole-syntax
   capability checks, quantities, laziness and count-accounting contracts.
2. Resolve the proposed byte-span operations' hosted metering, lowering,
   construction and composition gates **before implementation**. The accepted
   specification is not an available API or proof of sufficient throughput.
3. Obtain realistic buffered JSON decoding, then canonical frame-body handling,
   JSON-RPC envelope validation/response serialization and an end-to-end lifecycle.
4. Add versioned document storage, UTF-16 edits, a narrow typed compiler-service
   bridge, diagnostics, scheduling/cancellation and broader lifecycle behavior.

A meaningful next milestone is a measured end-to-end initialization exchange,
not another isolated parser-size pass. Public scoped-file source operations remain
disabled; there are no world-token, exactly-once, total heap/CPU or verified-backend
claims.

## Detailed records

- [Master merge validation and historical provenance](lsp-merge-validation.md)
- [Protocol foundations and acceptance](protocol-foundations.md)
- [Canonical framing](binary-framing.md), [header blockers](header-parser-blockers.md)
- [JSON diagnostic](json-iteration-adoption.md)
- [Workloads](lsp-workload-scaling.md), [cost audit](lsp-cost-audit.md)
- [Source-sharing candidate and timeout](lsp-source-sharing.md)
- [Byte-span specification — not implemented](byte-span-api-specification.md)
- Typed lifecycle source, contract and evidence: `tools/fixtures/lsp-lifecycle/`.

The Python reference implementation is included by the current `feature/lsp`
integration, not an implementation outside this branch. The earlier bootstrap-only
merge and its [validation record](lsp-merge-validation.md) remain historical
checkpoints. See the [Python LSP guide](lsp.md) for current server usage and the
[consolidation record](lsp-consolidation.md) for the earlier worker-lane merge.
