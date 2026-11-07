# Bounded LSP representation/cost audit — decision memo

**Scope: offline measurement and private admission fixtures only.** Base:
`afaf00c4c683a0e05c658a12c80a05d8e123201b`. No product source, core operation,
API, admission rule, parser cap, loop allowance or runtime budget changed. No
larger JSON input experiment was run. The separate byte-span lane is specification
only; nothing proposed there is implemented or benchmarked here.

## Decision

There are **independent syntax/construction and execution-representation blockers**.
Authorize at most a separately reviewed source-sharing/representation design next;
do not treat byte bulk operations as a sufficient fix or start their implementation.

1. Source lexical helper sharing is a concrete, policy-preserving candidate: the
   current checked JSON API contains **72 copies of the 19-node imported `orBool`
   RHS**; Frame contains **22 copies of the 31-node `equalString` RHS**. These are
   measured identical syntax fragments, not measured savings from a rewrite.
   Binding reusable helpers once and retaining abstract representation parameters
   could reduce actual checked syntax. No such rewrite was performed here, and
   wrapper/type expansion must be remeasured on the actual closed entry.
2. Typed representation deserves attention independently of byte scanning. The
   four-event full-ID entry has 7004 metadata nodes, 526 nodes under erased
   arguments and only 937 other computational-position nodes, yet admission
   counts **all 8467**. Repeated nominal descriptors/types dominate its syntax.
   Shorter names reduce nominal payload, not the node blocker. A compiler DAG
   storing the same tree more compactly would not automatically reduce its logical
   node count under today's policy.
3. Execution needs fewer closures/thunks/environments and cheaper byte/count
   representation, not just faster byte copying. Source state-field reconstruction,
   abstraction wrappers and per-byte scheduling remain expensive even on whitespace.
   A generic compact comparison/classification operation could address the string
   predicate's unary-octet path; existing Bytes slicing is already an immutable
   **native view**, not a copied suffix. A view API alone does not remove the unary
   position ledger. Buffered spans/blocks might avoid many callbacks for strings
   or whitespace, but token-dense transitions still need separate representation
   and token-builder work. There is no measured guarantee that any proposed
   combination fits the budgets.

**Policy boundary:** erasing metadata before initial admission would change
admission policy even if the number 8192 stayed unchanged. It is not an approved
source-sharing optimization. Preserve whole-syntax capability gates, including
**erased arguments, annotations and dormant branches**, before lowering; never
use this inventory to bypass them. Changing admission to count unique DAG nodes
would likewise be a policy change, not merely a storage optimization.

## Actual checked syntax and roles

[Normal evidence](assets/evidence/lsp-cost-audit.json) and
[sanitized evidence](assets/evidence/lsp-cost-audit-sanitized.json) contain nine
syntax inventories, six admission-only rows and four native profiles each.
The private Idris inventory reads `checkProject`'s actual term, counts every
constructor and descriptor/index/branch list cell exactly like `coreNodes`, and
checks its totals against `coreNodes` and saturated `payloadSize`.

| Entry | Nodes | Literal / nominal payload | Metadata | Under erased arguments | Other computational positions |
| --- | ---: | ---: | ---: | ---: | ---: |
| canonical echoFrame | 4341 | 70 / 0 | 2280 | 118 | 1943 |
| binary JSON API | 7467 | 461 / 576 | 3463 | 308 | 3696 |
| Read65 diagnostic | 8002 | 526 / 672 | 3773 | 358 | 3871 |
| typed transition API | 4359 | 0 / 3209 | 3611 | 323 | 425 |
| typed no-output consumer | 7033 | 36 / 4792 | 5879 | 345 | 809 |
| full-ID four-event handshake | 8467 | 38 / 5758 | 7004 | 526 | 937 |
| echo then fixed full typed observation | 11403 | 106 / 4792 | 8174 | 463 | 2766 |

Payload is **not all literal/wire bytes**: the conservative existing policy also
counts repeated nominal names, using host String length and Bytes length. The two
helper-alias entries have 39/27 nodes including their own main-binding wrapper;
the separately fingerprinted imported RHSs have 31/19 nodes respectively.
JSON's existing shared `equalString` binding leaves two matching imported RHSs,
versus Frame's 22. Counts do not mean those helpers execute only that many times.

Role labels are a **disjoint syntax inventory, not an executable erased term**.
Type roots, annotations and motives mark metadata; descendant roles inherit an
already noncomputational ancestor. Apply quantities use existing
`inferErased`/`weakHead` with proper binder contexts, and field quantities use the
same annotation shapes as `Core.Runtime`. Unknown inference is labelled unknown,
never assumed erasable; none remains in these entries' role totals. A lambda with
an erased parameter still has a computational body/closure. Both dormant branches
are counted. These are not reachability, soundness, live-memory or uniform-cost
proofs. `Core.Erased` is a checker, not an available erasure transformer; none was
invented or applied. `Core.Runtime` supplies usage rules, and `Native.Emit`
performs its existing annotation omission **after** original-syntax gates/checks
and admission.

The evidence includes per-constructor counts for every role, plus two distinct
repeat inventories. Structural shapes omit scalar fields; syntax fingerprints
retain variable indices, quantities, literal contents and nominal keys. Neither
captures surrounding free-variable meanings, proves semantic equivalence or grants
safe CSE. Overlapping repeats cannot be added as independent savings. For example,
the typed API repeats a 69-node VariantType fragment 17 times and a 49-node Sigma
fragment 21 times; the full-ID entry repeats them 28/34 times. These point to
representation duplication without licensing descriptor removal or weaker checking.

The Read65 term has 656 computational-position lambdas, 1136 Apply nodes and
1256 Variable nodes. The existing emitter generates **4031 C evaluator functions**,
including 701 `f_lambda` and 32 `f_erased` definitions. This is a different count:
the emitter omits annotations but still emits some erased-argument code whose
closures need not evaluate it. Neither count is an alternative admission size.

## Actual closed plumbing attempts: blockers, not composition passes

All modules are imported through an isolated source root; canonical Frame, JSON,
LSP and observation modules are copied byte-for-byte, never patched.

- `FullIdFour.fib` recreates the actual full observer with numeric ID `1`, then
  string ID `1`: source checking accepts, inventory measures **8467/5796**, and
  binary emission exits 1: `Native core admission exceeds 8192 nodes`. This fresh
  observation confirms the historical blocker, not a successful session or a
  requirement that future representations must fail.
- `EchoThenTyped.fib` checks at **11403 nodes**; native admission refuses it. This
  is an actual sequential closed term, including its 29 wrapper nodes beyond
  echo plus the existing 7033-node typed consumer. Its fixed typed request is
  **independent of the echoed frame**, not parsed from it.
- `JSONThenTyped.fib` attempts parsing fixed buffered `[]`, then a fixed typed
  request with a deliberately **control-only state demand**. Source checking
  exhausts the unchanged **200000 construction limit at its main declaration**;
  there is no accepted closed core size or native run to report.
- `EchoJSONThenTyped.fib` imports that probe after echo. Source checking exhausts
  construction while processing `LSP.transitionKernel`; again no checked size or
  execution. An earlier draft with the full observation module exhausted
  construction in `Observation.stateText`. Simplifying the observer did not close
  the construction blocker. Neither draft was a full-ID execution success.
- Existing Read65 and typed no-output entries still check/emit; their admission
  rows themselves are **not execution evidence** for those consumers. Only the
  four Read65 controls below execute in this audit.

There is no honest current frame-body-to-JSON-to-Event composition: canonical
Frame exports only `echoFrame`, not `withFrame`/read-body access. JSON returns
raw-lexeme tokens, not decoded strings/envelopes/typed events. An exposed body
continuation and a separately validated decoder boundary are missing APIs/work,
not permission to fake routing, change production Frame, or add a core primitive.
Control-only demands never replace the full-ID blocker in the evidence.
The arithmetic sum of isolated libraries is not a composed AST measurement; no
roughly 16k-node combined AST or its execution is asserted here.

## Counter-only native attribution: existing complete 64-byte inputs

Each case executes the **unchanged Read65** twice: existing private observer,
then private counter-attributed runtime. Exact outputs, all eleven original
metrics and successful return codes must agree; the existing JSON oracle checks
output. Both versions are repeated with ASan/UBSan. There are no extra forces,
fuel charges, changed decisions, larger caps or altered callback allowances.
The emitted-code mapping adds observer overhead: **no timing claim** follows.

| Whole input | Steps | Byte/Nat ledger steps | Variable / Apply / Lambda steps | Arena payload |
| --- | ---: | ---: | ---: | ---: |
| 64-token array | 97768 | 8983 | 30680 / 24238 / 22475 | 2998705 |
| ASCII string | 55660 | 16967 | 13063 / 10134 / 10409 | 1935876 |
| UTF-8 string (`ÿ`) | 67502 | 28871 | 13001 / 10134 / 10347 | 2500324 |
| whitespace + `1` | 43014 | 4745 | 12864 / 10143 / 10271 | 1343641 |

Every row consumes 64 logical adapter bytes and invokes 65 scanner callbacks.
These are actual whole-buffer diagnostic token transfers, **not JSON-RPC events**.
All step buckets sum exactly to the existing step total. Buckets are immediate
sites, not inclusive costs: generated operation evaluation, natural ledger,
fold/IO visits, and the existing bulk UTF-8 length charge (608/360/360/328 steps).
Variable evaluation can force later operations; nested work belongs to its own
bucket, not to the variable again. No charge is hidden or newly introduced.

For the 64-token row the allocation partition is:

- **25212 thunks / 1613568 payload bytes**;
- **30065 values / 962080 bytes**, including **22475 closure values**;
- **26057 environment cells / 416912 bytes**;
- append buffers 5988 bytes, String append 60, pending nodes 96, octet storage 1.

These sum exactly to **2998705** retained arena payload bytes. Value-tag counts
are a second, overlapping marginal, **not additional allocation bytes**. All four
inputs construct 582 pairs and 259 nominal wrappers; the scanner has a four-field
record (`rest`, `stack`, `mode`, `tokens`), sharing/reboxing and explicit field
demands. Pair/closure counters include other wrappers too; this observer does not
pretend to identify every allocation with a specific source state field. It does
show repeated record/closure construction rather than large copied byte buffers
as the principal arena cost. Even whitespace allocates over 1.3M payload bytes.
Arena payload excludes allocation headers, allocator overhead, transport storage,
compiler memory and peak/live heap; native slices retain backing storage until
session teardown. It is not a memory-leak or persistent-session measurement.

The 3681-byte/720-token initialize target was **not executed by JSON here**.
Read65 denial on larger input consumes only 65 bytes and never profiles its
suffix; historical denials are not used as full-message profiles. The 64-token
row already spends 97768/100000 steps and retains about 3M arena payload bytes.
No extrapolated larger-message execution, larger cap/loop experiment or promise
that bulk operations alone fix either this arena cost or typed syntax follows.

## Reproduction and validation

Use only this worktree's private build/prefix and existing pinned tools:

```sh
source /tmp/fibril-iteration-env.sh
export IDRIS2_PREFIX="$PWD/build/test-prefix"
make -j8 build PACK=/tmp/fibril-foundations-pack
"$IDRIS2" --install fibril.ipkg
installed=$("$IDRIS2" --dump-installdir fibril.ipkg)
export IDRIS2_PACKAGE_PATH="$(dirname "$installed"):$IDRIS2_PACKAGE_PATH"
mkdir -p build/lsp-cost-audit
cp tools/fixtures/lsp-cost-audit/Audit.idr build/lsp-cost-audit/
printf 'package lsp-cost-audit\nsourcedir = "."\ndepends = fibril, yaml\nmain = Audit\nexecutable = audit\n' > build/lsp-cost-audit/audit.ipkg
(cd build/lsp-cost-audit && "$IDRIS2" --build audit.ipkg)
python3 tools/probe_lsp_cost_audit.py \
  --audit "$PWD/build/lsp-cost-audit/build/exec/audit" \
  --output build/lsp-cost-audit-normal.json
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  python3 tools/probe_lsp_cost_audit.py \
    --audit "$PWD/build/lsp-cost-audit/build/exec/audit" \
    --output build/lsp-cost-audit-sanitized.json
python3 tools/test_lsp_cost_audit.py
python3 tools/test_lsp_workload.py
python3 tools/test_json_oracle.py
```

Pinned Idris executable:
`/Users/odunadeboye/.local/state/pack/install/74b33730b6fea649b15e8d01ab099df9effcc7a0/idris2/bin/idris2`.
The evidence records source hashes (including all compiler/runtime sources),
compiler **launcher and Chez image** hashes separately, private audit launcher/image
hashes, private instrumented-copy hashes and compiler/platform versions. These
are new-run provenance, not retroactive repairs to historical launcher-only hashes.
Normal and sanitizer observation rows, source and instrumented-copy hashes match;
only compiler invocation metadata differs. Sanitizers cover both emitted native
variants on all four controls, not the hosted compiler/FFI or an LSP server.

All measurement launches reuse the fixed owned-unreaped-anchor `run_process`
helper. Inputs are complete buffers followed by EOF, never live/open-stdin
claims. Execution deadlines are 90 seconds; other launches 120 seconds; cleanup
bounds/platform/credential exclusions remain those documented in
[LSP workload scaling](lsp-workload-scaling.md). File errors, unexpected diagnostics,
timeouts, sanitizer findings, output differences and unbalanced counters fail the
probe, never count as represented parser rejection or a feature pass.

The five new offline regression groups check constructor coverage/quantity rules,
disjoint role/list-cell accounting and syntax-versus-shape distinction, exact
full-ID fixture regeneration and unchanged imports, fail-closed counter insertion,
and both evidence files' totals/provenance/blocker labels. All five passed, as did
19 existing workload groups, eight JSON oracle tests, Python compilation, direct
pinned Idris mkdoc, handbook generation/local-link checking and 16 handbook tests.
Final fresh normal and sanitized probes passed their audit assertions; the feature blockers remain
failures to compose/admit. Initial drafts failed a missing private-helper import,
construction checks, a profiler total assertion (the existing UTF-8 bulk charge
was initially omitted), and offline test setup/assertions. They were corrected
and are not counted as successful final observations. No final timeout or budget
increase occurred. Full repository/editor/large-JSON execution is not claimed.

**Recommended next gate:** review these measurements, then choose a bounded
representation/source-sharing design with explicit unchanged whole-syntax gates.
Require actual construction/admission plus allocation measurements again before
approving byte-operation implementation or a genuine decoder/framer API slice.
