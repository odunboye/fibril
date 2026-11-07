# Two lexical helper aliases — candidate milestone

**Recovery checkpoint; initial agent run failed its 1800000 ms orchestration
deadline.** Logged observation passes below do not turn that overall failure into
a pass. A single bounded recovery retry packaged the existing work and reran only
cheap offline checks; it did not rerun observation matrices, framing suites or
private compiler builds. Parent review/integration remains pending.

**Candidate only, based on `5ca14f3`.** This is accepted-source preservation,
not a full grammar formal proof, production rollout, wire composition or an LSP
implementation. [Normal evidence](assets/evidence/lsp-source-sharing.json) and
[ASan/UBSan evidence](assets/evidence/lsp-source-sharing-sanitized.json) record
fresh checks and executions. The [accepted audit](lsp-cost-audit.md), its evidence,
production Frame, JSON64 diagnostic and historical shared parser are unchanged;
the existing audit hash-provenance regression still passes.

## Exactly two source changes

The explicit root `tools/fixtures/lsp-source-sharing` contains **the same logical
module names**, including `Protocol.Frame` and `Protocol.JSON`. Tests explicitly
select that root; no standard example, CLI default or production import changes.
All its other source/adapter files are byte copies of the existing fixtures.

- Frame binds `sharedEqualString` once inside `echoFrame`, then refers to it in
  place of the 22 original `equalString` references.
- JSON binds `sharedOrBool` once inside `parseJSONKernel`, then refers to it in
  place of the 72 original `orBool` references. Its existing `sameText` binding
  of `equalString`, including the binary adapter's separate comparison, stays intact.

Both aliases are **unrestricted function values with linear arguments**:
`(1 left : String) -> (1 right : String) -> Bool` and
`(1 left : Bool) -> (1 right : Bool) -> Bool`. This does not promote a linear
result/value to unrestricted use. The original imported function RHSs are verified
closed (31 and 19 nodes), the actual alias value binders have quantity unrestricted,
and the ordinary source/runtime type checker accepts each actual closed client.

No grammar, unicode/surrogate/control validation, raw token spelling, header
policy, source API, core/runtime operation, cap, depth/count allowance or budget
is altered. The original pure Nat fold and binary buffered runner instantiate
exactly the same transition/finalizer as before. The cap remains 64 bytes; no
larger JSON-cap/count experiment is run.

### Preservation checks, not occurrence-count evidence

`tools/lsp_source_sharing.py` removes only the exact introduced binding and
inverses complete reference-name tokens outside strings/comments. It demands
**byte-exact baseline source** afterward. Freshness against every baseline token
precludes capture or shadowing of the new name. Substantive edits, extra source,
quantity edits and changed literals fail this check.

Separately, `Audit.idr` inventories the **actual checked closed terms**. For each
accepted baseline/candidate pair, the checker expands exactly one unrestricted
alias application whose argument is the identical verified closed imported RHS
and whose domain has the original checked linear-argument type. Removing this
binder substitutes only its references and shifts outer de Bruijn indices;
Lambda/Pi/Sigma body scopes are handled explicitly. Every other constructor and
scalar (including indices, quantities, literals and nominal names) must match
exactly. No other beta reduction, grammar rewrite or equivalence oracle is used.
Synthetic tests cover local/outer indices under all three intrinsic binders,
closedness, quantity/type refusal and refusal to normalize arbitrary redexes.
This is a focused executable preservation check of the accepted sources/entries,
not a formal theorem about all source programs or all JSON inputs.

## Actual closed entries and construction accounting

All nodes include original metadata, annotations, erased and dormant syntax.
Payload is the existing total literal **plus nominal** policy estimate, not wire
size. No pre-admission erasure/DAG policy is used.

| Closed entry | Initial nodes baseline → candidate | Payload (both) | Construction debit baseline → candidate |
| --- | ---: | ---: | ---: |
| Frame Main | 4341 → 3719 | 70 | 52863 → 51509 |
| Frame Two | 4364 → 3742 | 70 | 52909 → 51555 |
| pure JSON API | 6205 → 4935 | 892 | 145990 → 136828 |
| binary JSON API | 7467 → 6197 | 1037 | 148514 → 139352 |
| PureRead65 | 6674 → 5404 | 1005 | 164522 → 155360 |
| Read65 | 8002 → 6732 | 1198 | 167178 → 158016 |
| EchoThenTyped | 11403 → 10781 | 4898 | 186813 → 185459 |

Construction debit is **not allocations or AST size**. A private generated
`CountedModuleCheck` clone reports the existing named-module declaration estimate
debits plus the final `main.size` reservation:
`(200000 - compiled.remaining) + main.size`. Evidence includes these two components
separately; in these entries the latter equals the checked closed node count.
Unique exact insertion seams fail closed. No budget subtraction, estimator,
typing/reduction decision or admission rule is changed. Every accepted counted
inventory must equal the ordinary checker's entire inventory JSON after removing
only the counter fields, not merely have the same size.

**Blockers remain, not composition passes:**

- EchoThenTyped still fails native admission at **10781 > 8192** nodes. It is
  actual sequential opaque echo then an independent fixed typed full observation,
  not a typed demand derived from the echoed body. It is not executed here.
- JSONThenTyped still fails construction at `main`. Baseline has 7778 remaining
  and saturated declaration estimate 7791; candidate has 14400 remaining and
  estimate 14413. These are actual saturation results, **not** exact unsaturated
  declaration totals. There is no checked closed node/payload size or native run
  for either. Its fixed `[]` then independent typed request uses a control-only
  state demand; it does not replace the historical full-ID blocker.

No further factoring, Source CPS, API/core extension or body callback is added.
`echoFrame` is only opaque echo. There is no frame-body-to-JSON-to-Event composition,
wire envelope/ID decoder, sum of isolated savings or claim that these aliases
resolve typed representation/construction blockers.

## Executed native work and effects

Both existing observer and counter-attributed private runtimes execute every row;
outputs, return codes and **all eleven original metrics** must agree. Allocation
partitions and immediate step buckets balance exactly. Each is repeated under
ASan/UBSan. The two runs' syntax, source hashes, matrix rows and native metrics/
partitions match; launcher/images are independently fingerprinted. Counter
instrumentation adds no forces/charges and does not justify timing claims.

| Complete input | Steps baseline → candidate | Arena payload baseline → candidate | Callbacks (both) |
| --- | ---: | ---: | ---: |
| JSON 64-token array (64 bytes) | 97768 → 95602 | 2998705 → 2894705 | 65 |
| ASCII string (64 bytes) | 55660 → 55648 | 1935876 → 1935268 | 65 |
| UTF-8 `ÿ` string (64 bytes) | 67502 → 67490 | 2500324 → 2499716 | 65 |
| whitespace then `1` (64 bytes) | 43014 → 42399 | 1343641 → 1314089 | 65 |
| opaque 4096-byte frame body (4120 wire bytes) | 19671 → 19539 | 529977 → 523609 | 0 |

For dense64, thunks change **25212 → 24490**, environment cells **26057 → 25335**,
values **30065 → 28620**, closures **22475 → 21030**. The existing unary byte/Nat
ledger remains **8983 steps**. Both runs still construct **582 pairs** and **259
nominal wrappers**. Frame's byte/Nat ledger remains **16408 steps**; closures change
952 → 863. These are marginal observed counters, not inclusive costs or independent
additive savings. Arena payload is retained payload, excluding headers, allocator/
compiler/transport overhead and peak/live heap; this is not a persistent-session
or leak measurement.

Effects remain identical for each pair:

- JSON controls: one read/write/flush, 64 consumed bytes, 65 scanner callbacks;
  accepted bytes 124/66/66/3, requests 2, reserved capacity 189/131/131/68.
- Framing: eight reads, one write, two flushes including session finalization,
  ten requests, 4120 consumed/accepted bytes and 8240 reserved capacity. No binary
  iteration callback or JSON execution is involved in that opaque echo.

## Validation and reproduction

Normal **and** sanitized runs each execute the complete existing **120-case JSON
matrix** on hosted and emitted native: **76 valid, 43 invalid, 1 reader EOF per
backend**, no budget rejection accepted as a parser match. The independent Python
oracle is used only for expected raw token transfer. The source parser itself is
checked/emitted/executed; there is no Python state handler or C grammar substitute.
Named real-stdio cases also run through the hosted CLI and emitted native binary.

All **14 framing regressions** run on the candidate imports, including every
existing size/truncation/header/octet boundary, bulk request/capacity accounting,
two-frame flush sequencing and live fragmented-open-input behavior. Whole-buffer
launches use the fixed owned-unreaped-anchor EOF helper. Only actual early-refusal,
flush and fragmentation tests retain their own bounded live processes. No
background sleeping poll, unrelated kill or shared/worktree cache cleanup is used.

Negative controls reject malformed candidate source and a missing alias helper;
substantive non-alias source changes fail preservation. The actual nonempty parsed
`[1]` source term passes binary execution with **zero parser transport effects**
(four callbacks; zero reads/writes, one final session flush), while its inappropriate
CLI `run`/`emit-c` and actual whole-syntax interactive/resource paths reject it.
The hosted matrix also exercises the latter two gates on every real checked term.
These are runtime/gate results, not assertions inferred from source text.

```sh
source /tmp/fibril-iteration-env.sh
export IDRIS2_PREFIX="$PWD/build/test-prefix" PACK=/tmp/fibril-foundations-pack
make -j8 build PACK=/tmp/fibril-foundations-pack
python3 tools/probe_lsp_source_sharing.py --output build/lsp-source-sharing-normal.json
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  python3 tools/probe_lsp_source_sharing.py --output build/lsp-source-sharing-sanitized.json
python3 tools/test_lsp_source_sharing.py
python3 tools/test_lsp_cost_audit.py
python3 tools/test_json_oracle.py
```

Pinned Idris:
`/Users/odunadeboye/.local/state/pack/install/74b33730b6fea649b15e8d01ab099df9effcc7a0/idris2/bin/idris2`.
The probe installs only into this worktree's private `build/test-prefix` and builds
private audit tools in `build/lsp-source-sharing`. It records all compiler/runtime,
candidate/baseline and executing probe/adapter source hashes, compiler launcher/
Chez-image hashes before/after staging, private helper launcher/image hashes,
private instrumented C hashes and tool/platform versions. Staging can regenerate
Chez images; their binary hashes need not be reproducible across installs even
when sources and all checked/executed observations match.

The preserved pre-timeout normal/sanitized logs record completed observation
passes: respectively four JSON groups in 87.874/84.279 seconds and fourteen
framing groups in 77.459/80.027 seconds, followed by `Candidate observations
complete`. Each log records the full 76-valid/43-invalid/1-reader-EOF totals on
both backends. These are logged suite passes, **not an overall agent-task pass**.
Eight new offline regression groups, five accepted audit groups and eight oracle
groups passed before timeout and were cheaply rechecked during recovery.

The cached commands used the environment above and the two explicit probe
commands shown, writing `build/lsp-source-sharing-normal.json` and
`build/lsp-source-sharing-sanitized.json`; their logs are
`/tmp/lsp-source-sharing-normal.log` and `/tmp/lsp-source-sharing-sanitized.log`.
The committed evidence files are byte-identical to those cached build outputs.
During recovery, all **167 recorded input source hashes in each evidence file**
matched the current files, including candidate README and executing Python
scripts/tests. No runtime provenance was rewritten or inferred retroactively.
Only this unmeasured narrative document changed after evidence capture.
The preserved pre-retry checkpoint is
`/tmp/fibril-lsp-source-sharing-timeout-checkpoint.tar.gz`, SHA256
`6e7c346a1e151e9be5ff426c5d590f806e0c375525120daad5a608299b6f10e5`.

An initial probe
invocation exposed an unsupported `cwd` wrapper; it was fixed to use the owned
helper. One early aggregate launch hit its outer 120-second tool deadline after
the matrix, and is **not counted as a complete pass**; final foreground aggregates
used a 600-second outer deadline with unchanged per-child 90/120-second bounds.
A draft construction counter used ambiguous infix arithmetic; explicit arithmetic
and separately balancing debit/reservation fields replaced it before final evidence.
The completed observation logs show no per-child timeout, budget increase or
sanitizer finding; nevertheless the enclosing **agent run timed out and failed**.
No cap expansion, full LSP execution, integration or retrospective overall pass
is claimed.

**Next gate:** independent review of this candidate-only preservation milestone.
Keep the construction/node blockers visible; decide separately whether any
production adoption or subsequent representation/API work is warranted.
