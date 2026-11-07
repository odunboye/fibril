# LSP-shaped workload and bulk-byte decision proposal

**Evidence/proposal only, based on `83aba54`. No runtime/API implementation is
approved or delivered here.** Production framing, parser diagnostic caps, loop
counts, admission, evaluator/arena budgets and transport are unchanged. This does
not implement JSON-RPC dispatch, generalized headers, a production JSON parser or
an LSP. The parallel typed-event lifecycle is not decoding evidence.

## Provenance and reproducible corpus

`tools/generate_lsp_workload.py` is an **offline generator/oracle**.
`tools/fixtures/lsp-workload/` contains exact compact UTF-8 `.json` bodies (no
extra newline), canonical `.frame` files, and `manifest.json`. `.gitattributes`
prevents Git newline conversion of frames. The frame is exactly
`Content-Length: <UTF-8 byte count>\r\n\r\n<body>`. Expected fields use recursively
tagged `object_members` lists, not dictionaries: duplicate members, their values
and their order survive at every nesting level. Arrays stay arrays. The manifest
also contains hashes, all method/JSON-RPC/id occurrences and id kinds. Duplicate
id is explicitly an ambiguity probe, **not** a chosen last-wins dispatch policy.

Read-only reference inspection, not reference-server execution:

- `../fibril-lsp` HEAD `9e87c0d43473d54749581cdd3004ad812068d15d`.
- `tools/test_lsp.py`: `Client` lifecycle/serialization/open/full-change shapes,
  incremental-coordinate tests. SHA256
  `5c09b496a5175265a9d9c730fbfdacb8d0b2b9ed7fb47333c7d98cf217fd7e4b`.
- `tools/fibril_lsp.py`: `Positions`, `changed_text`, size/framing contracts.
  SHA256 `92904f4f8dc13acfe297c11722bf5ec0f0f6cfd88b415d8d685c5e1dd491bb3d`.
  Its 8 MiB frame/65536 source-byte limits are **not** adopted here.
- `editors/nvim/lua/fibril/init.lua`: merges Neovim's
  `make_client_capabilities()` with user overrides; no fixed capability dump.
  SHA256 `8230c478d314a705a240ca57a1828495308017815d72da4c112d6c71861cbf24`.

**None of the corpus is actual captured client traffic.** `reference-derived`
means hand-generated from the above shapes, with deterministic anonymous paths
and compact serialization (the reference client uses spaced Python JSON).
`synthetic` means explicitly constructed capabilities/document/boundary inputs.
The capability fixture is meaningful Neovim-shaped LSP data, not a claim about
any exact Neovim release's wire output. Reference files, main and other worktrees
were not edited; no reference client/server or Neovim was launched.

The small ordered session is initialize/initialized/didOpen/didChange/shutdown/
exit. Large/boundary cases are independent scaling probes, not one coherent
version sequence. All paths are `file:///workspace/anonymous/...`; process id is
null, and no real usernames, buffers or paths are captured. Non-ASCII contents
include α, astral emoji and combining accents with CRLF. The incremental change
replaces 🌍 at UTF-16 `[18,20)` on line 1 by `🧵λ`, then replaces `é` at updated
`[21,23)` by `é`. The offline test applies both strictly without splitting a
surrogate and expects `main = putStrLn "α🧵λé"`. These are coordinate/oracle checks,
not Fibril edit-runtime execution or source compilation checks.

Tokens below count every punctuation, object key/string, number and literal;
whitespace is excluded. Nesting counts open objects/arrays, root included. This
is the diagnostic lexeme convention, **not** semantic-token or AST-node counts.
All bodies are whole-syntax/scalar-Unicode validated offline before token counts.

| Body | Provenance | Body bytes | Wire bytes | Tokens | Nesting | Method / id kind |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| initialize-reference | reference-derived | 247 | 270 | 54 | 5 | initialize / number 1 |
| initialized | reference-derived | 52 | 74 | 14 | 2 | initialized / absent |
| didOpen-unicode | reference-derived | 219 | 242 | 33 | 3 | textDocument/didOpen / absent |
| didChange-utf16 | reference-derived | 373 | 396 | 105 | 6 | textDocument/didChange / absent |
| shutdown | reference-derived | 56 | 78 | 18 | 2 | shutdown / number 2 |
| exit | reference-derived | 45 | 67 | 14 | 2 | exit / absent |
| shutdown-string-id | synthetic | 69 | 91 | 17 | 1 | shutdown / string shutdown-2 |
| initialize-capabilities | synthetic | 3681 | 3705 | 720 | 8 | initialize / number 1 |
| didOpen-large | synthetic | 5919 | 5943 | 33 | 3 | textDocument/didOpen / absent |
| didChange-large | synthetic | 5920 | 5944 | 35 | 4 | textDocument/didChange / absent |
| didOpen-boundary-4095 | synthetic | 4095 | 4119 | 33 | 3 | textDocument/didOpen / absent |
| didOpen-boundary-4096 | synthetic | 4096 | 4120 | 33 | 3 | textDocument/didOpen / absent |
| didOpen-boundary-4097 | synthetic | 4097 | 4121 | 33 | 3 | textDocument/didOpen / absent |
| duplicate-fields | synthetic ambiguity | 78 | 100 | 29 | 2 | shutdown / string s-1, then number 7 |

Every `jsonrpc` occurrence is string `2.0`. The 3681-byte initialize has real
synchronization, UTF-16, workspace edits, definitions/links, diagnostics, completion,
rename and semantic-token capability structures. It already has **720 > 512**
lexical tokens; silently selecting 512 would exclude this fixture even below
4096 bytes. Small token count does not imply small text: large document messages
have 33/35 tokens but exceed 4096. Conversely wire bytes can exceed 4096 while the
4096-byte **body** remains inside today's framer policy. No new product cap is
selected here; reference-shaped buffers disprove neither cap's intentionality,
but show why a blind 4096 message limit is not a realistic workload solution.

## Executed bounded baseline observations

The worktree's own freshly built CLI checked/emitted the unchanged canonical
`examples/modules/binary-frame/Main.fib` and diagnostic
`tools/fixtures/json-iteration/Read65.fib`. The probe uses the existing
`test_binary_iteration.observe` counters in private runtime copies and a C
byte-adapter harness with **no header/JSON grammar**. It records steps, peak pure
depth, retained arena payload, callback/read/write counts, logical consumed and
accepted bytes, flushes, requests and reserved capacity. Native FILE prefetch is
not logical protocol consumption or a raw-descriptor handoff guarantee. Hosted
consumption is not instrumented; supplied length is never claimed consumed.
Arena payload is not total heap/live memory/session storage.

[Normal evidence](assets/evidence/lsp-workload.json) and
[ASan/UBSan evidence](assets/evidence/lsp-workload-sanitized.json) contain identical
64 observation rows and three independently measured entry sizes. Evidence also
fingerprints the private compiler and eight unchanged production/diagnostic source
files; offline tests recheck the source hashes. Sanitizers cover both emitted
native executables and all32 native rows, **not** the hosted compiler/FFI; the32
hosted rows were repeated without sanitizing that compiler. Each backend ran14
framer cases and18 diagnostic cases (14 fixtures plus four controls):

- Framer: **11 opaque echoes, three body-cap rejections per backend**. Echo is
  framing success only, not JSON parsing or envelope validation. Oversized
  4097/5919/5920-byte bodies reject after **20 logical native header bytes**;
  no body, write or flush. Sending the whole frame does not mean it was consumed.
- JSON diagnostic: only initialized/shutdown/exit fit 64 bytes and transfer whole
  raw-lexeme token streams. All **11 larger fixture bodies** produce the one-byte
  diagnostic denial. Native Read65 consumes **65 bytes only**, has **zero scanner
  callbacks**, costs689 steps and reserves66 bytes. This is **not** whole-message
  parsing/profiling, even for the 4096/5919-byte inputs. It says nothing about
  their unconsumed suffix's syntax or eventual parse cost.
- Four existing-profile controls (64-token array, ASCII string, UTF-8 string,
  whitespace-plus-value), each exactly64 bytes, genuinely scan the entire input
  on both backends. No larger diagnostic cap or allowance was tried.

There are 22 opaque echoes, six framer cap rejections, 22 diagnostic cap denials
and 14 whole-buffer token transfers across both backends. Zero recorded runtime
budget failures, mismatches, deadlines or sanitizer findings in the **final**
matrices. Fourteen transfers include eight control rows, not fourteen decoded
LSP requests. All64 rows have `whole_jsonrpc_decoded: false`.

Selected **executed native** profiles (body bytes, not all wire bytes):

| Entry / input | Body bytes | Steps | Peak pure depth | Arena payload | Callbacks | Logical consumed | Requests / capacity |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Framer / realistic initialize | 3681 | 17795 | 121 | 480673 | 0 | 3705 | 10 / 7410 |
| Framer / boundary4096 | 4096 | 19671 | 126 | 529977 | 0 | 4120 | 10 / 8240 |
| Framer / boundary4097 denied | 4097 | 1620 | 33 | 58464 | 0 | 20 | 5 / 20 |
| Read65 / initialized | 52 | 48480 | 70 | 1614534 | 53 | 52 | 2 / 127 |
| Read65 / shutdown | 56 | 53842 | 83 | 1776755 | 57 | 56 | 2 / 135 |
| Read65 / exit | 45 | 42431 | 70 | 1401840 | 46 | 45 | 2 / 120 |
| Read65 / ASCII string | 64 | 55660 | 70 | 1935876 | 65 | 64 | 2 / 131 |
| Read65 / UTF-8 string | 64 | 67502 | 70 | 2500324 | 65 | 64 | 2 / 131 |
| Read65 / whitespace +1 | 64 | 43014 | 75 | 1343641 | 65 | 64 | 2 / 68 |
| Read65 / 64-token array | 64 | 97768 | 81 | 2998705 | 65 | 64 | 2 / 189 |

Successful framer entries perform an explicit flush and mandatory success flush
(two adapter flushes); diagnostic entries only the mandatory flush. Requests
include explicit flush, capacity reserves full read capacity, including short
input. These semantics are unchanged.

Closed-entry source measurements: framer **4341 nodes/70 literal payload**;
Read65 **8002/1198**; binary JSON API **7467/1037**. Read65 has only190 nodes of
8192 headroom. The API alone leaves725. Adding4341+7467=11808 is **not** a
composition measurement: lexical sharing and wrappers can change that total.
No combined framer+JSON+typed-event entry was constructed or admitted.

Inspected prior evidence, **not rerun by this task**: the accepted header
investigation's semantically weakened control still costs331 native steps per
padded byte; the preserved scanner exhausts100000 at182/1024 reads. A lookup-only
improvement is insufficient. At4096 bytes even spending the entire100000 budget
allows only24.4 steps/byte before fixed costs; this is a feasibility yardstick,
not an extrapolated execution. The raw count-entry ledger for length4096 is
8194 > hosted4096, before callbacks. Nested loops do not reset session work or
arena. See [header blockers](header-parser-blockers.md) and
[JSON adoption](json-iteration-adoption.md). No throughput has been solved.

## Narrow proposal for parent decision — NOT an available API

Recommend a **separately reviewed design/cost spike for buffered byte blocks and
class spans**, not a lookup-only primitive, new transport, native JSON/header
parser, larger budget, or immediate larger-cap parser. The proposed surface is
generic byte manipulation plus an explicitly binary-effectful buffered iterator.
All names/types below are semantic sketches, not approved executable signatures:

1. **Compact byte extents and immutable views.** Obtain an opaque `ByteExtent`
   alongside a retained/shared Bytes value; an extent represents0..65536 without
   allocating unary Nat. Provide checked split/compare/remaining operations,
   returning immutable prefix/suffix views and extents, not public pointers.
   No implicit extent-to-unary-Nat conversion. A negative/out-of-range split is
   a distinct data failure, never clamped or silently truncated. Source chooses
   the product quota; the primitive's65536 ceiling is the existing chunk ceiling,
   **not** a proposed message policy. Extents above that require a separate design.
2. **Reusable byte-class table and maximal span.** Validate exactly256 table
   octets, each0/1, once into a shareable immutable `ByteClass`. A generic
   `spanByteClass` on a view returns the longest matching prefix and exact rest;
   empty input/match are ordinary data. It does not consume a nonmatching octet.
   Invalid table is data failure with ownership consumed, no valid class produced.
   Tables express arbitrary byte sets, not CRLF, names, escapes or JSON states.
   Source retains all grammar, decimal uniqueness/bounds and Unicode decisions.
   Mapping/casefold or lookup is **not** smuggled into this first surface; if
   needed it requires its own cost justification. Bounded source header policy
   remains blocked rather than weakened to fit this proposal.
3. **`iterateByteBlocksBinary` over an already-buffered view.** Explicit state/
   result types and linear payload, using existing Done/Continue/Exhausted
   distinctions. Positive block width1..32, explicit compact byte quota, and
   explicit small callback allowance; none comes from decoding a whole4096-deep
   Nat. The runtime assigns at most `min(width, remaining input, remaining quota)`
   bytes per callback and advances once; no copying/re-reading prefix. Quota and
   callback allowance are both session-local monotonically decreasing values,
   not renewed by block/line boundaries. Zero allowance invokes no callback.
   Quota exhaustion and end-of-buffer are distinct returned reasons carrying
   state and **all unassigned suffix bytes**. A callback Done consumes its assigned
   block and returns its result plus unassigned suffix; it never claims an
   unexamined suffix validated. If a source parser needs to finish inside a
   block, its result must explicitly retain that block's remainder via the view
   split API. It must account that remainder alongside the outer suffix. Callback
   state WHNF follows accepted iteration, not arbitrary deep strictness. This is
   binary-effectful even with pure callbacks; pure reducers remain unchanged.

The three pieces must be reviewed as one minimal performance experiment: compact
counts remove the known ledger trap; spans avoid per-octet source callbacks for
long strings/whitespace; blocks bound work between source control decisions.
**There is no evidence yet that these operations suffice** for escape-dense JSON,
720-token capabilities or composed headers. Per-token allocation and grammar
transitions may still dominate. Do not add arbitrary parser opcodes to compensate.
An alternative source/compiler representation change may be preferable; the
parent may reject this surface before any core edits.

### Required semantics and gates before implementation approval

- **Lifetime/immutability:** views retain the backing storage through subsequent
  reads, block callbacks and retained results. Hosted and native must agree on
  Bytes linear consumption/sharing. Native views cannot point into a recycled
  scratch buffer or freed callback frame. Session-backed views may not escape
  session teardown; any supported owned promotion must be explicit and charged.
  Define destruction order and bounds on retained backing buffers; a tiny view
  pinning a full input is an arena/session-memory risk, not free O(1) storage.
- **EOF/error/overread:** these proposed operations do **no transport IO**. Empty
  buffered input is data, not EOF. Existing `primReadBytes` remains fill-capacity
  or EOF/error with existing short-prefix/fatal-error semantics and reservations;
  it is not silently changed into read-some/read-until. There is no implicit
  refill, rollback, cross-frame drain or new read-until operation. Buffered suffix
  must be returned explicitly, never dropped or rediscovered by reading stdin.
  Whole JSON needs the declared full body before acceptance. Generalized live
  headers still need a separate buffering/transport decision: a wide existing
  fill-capacity read could wait across a short complete header while stdin stays
  open. This proposal does not claim to close that blocker.
- **Accounting:** charge table validation per256 entries once; charge each inspected
  byte of a span (including a failing class test), bound-check/view/extent creation,
  callback application, assigned block scheduling and finalization. Never hide
  scans under one flat evaluator step or reset100000 steps/16MiB arena on blocks.
  Quota charges assigned bytes even on early Done; scanning repeated views spends
  work again. No transport request/capacity is spent by buffered operations;
  actual outer reads/writes/flushes retain current reservation rules. Specify
  hosted fuel and native depth/steps/arena costs consistently before code. An
  uncharged O(N) C scan or large unary quota construction is unacceptable.
- **Complexity:** intended scan cost O(inspected bytes), table setup O(256), view
  split O(1) metadata, and callback count bounded by both explicit allowance and
  assigned blocks. These are design targets, not current guarantees. Repeated
  concatenation/token construction, revalidation of classes per token, nested
  views, lazy aliases, decoded string assembly and spans that repeatedly rescan
  suffixes can still be quadratic or exceed the arena. Track allocations/retained
  storage and all field forcing, not WHNF alone. No assumption that raw token
  lexemes provide decoded strings or UTF-16 edit coordinates.
- **Whole syntax:** source must check complete UTF-8/scalar validity, controls,
  escapes and surrogate pairs, number grammar, nesting/tokens and trailing data
  across block boundaries, including invalid overwritten duplicate values. Header
  source must eventually check strict framing/length uniqueness/decimal bounds
  and any separately approved optional-header policy. Envelope validation must
  separately handle absent/null/string/number ids and duplicate policy. No early
  accept when the first top-level value ends; cap refusal remains distinct from
  grammar rejection/exhaustion/EOF. Source-level invalid results do not fabricate
  tokens or count as dispatch success.
- **Source composition:** check the *actual closed entry* importing framer, byte
  operations, source JSON finalizer and typed-event consumer under8192 nodes and
  200000 construction units before protocol execution. Record literal payload,
  wrapper expansion, shared helper placement and native/hosted equivalence. An
  isolated API fitting is insufficient. No admission exemption or budget increase.
- **Acceptance experiment, only after permission:** retain all64-byte grammar
  oracle tests, differential/sanitizer lifetime tests with distinct later reads,
  open-stdin/fragmentation/truncation/error cases at outer framing, block splits
  inside UTF-8/escapes/CRLF/numbers, duplicate nesting and unconsumed-suffix checks.
  Use measured worst-shape profiles (token-dense, escape-dense, long keys/string,
  capability structures), not only padded text. Larger diagnostic cap/loop-count
  experiments require **separate explicit approval first**. Success means full
  supplied body examined, exact expected fields/tokens, no hidden budget denial,
  correct request/capacity/arena ledgers, and admitted composition; no deadlines
  counted as passes. Larger product body/token policies need an explicit decision
  informed by the above corpus, not blindly4096/512.

**Decision boundary:** deliver this corpus/profile checkpoint first. Authorize at
most a specification/cost spike separately; do not start core/API implementation,
cap experiments, new IO/lookup primitives or a production LSP claim from this
report. No implementation beyond offline tooling was attempted.

## Validation and reproduction

Python3.10+; use only this worktree's private build/test prefix. The pinned compiler
and curated dependency environment already existed; no shared install/cache writes
or cleanup were performed. Commands below build the CLI and existing Measure
helper locally (do not borrow another writer's executable):

```sh
source /tmp/fibril-iteration-env.sh
export IDRIS2_PREFIX="$PWD/build/test-prefix" # override inherited other-worktree prefix
make -j8 build PACK=/tmp/fibril-foundations-pack
"$IDRIS2" --install fibril.ipkg
installed=$("$IDRIS2" --dump-installdir fibril.ipkg)
export IDRIS2_PACKAGE_PATH="$(dirname "$installed"):$IDRIS2_PACKAGE_PATH"
mkdir -p build/lsp-workload-measure
cp tools/fixtures/json-admission/Measure.idr build/lsp-workload-measure/
printf 'package lsp-workload-measure\nsourcedir = "."\ndepends = fibril, yaml\nmain = Measure\nexecutable = measure\n' > build/lsp-workload-measure/measure.ipkg
(cd build/lsp-workload-measure && "$IDRIS2" --build measure.ipkg)
python3 tools/generate_lsp_workload.py --check
python3 tools/test_lsp_workload.py
python3 tools/test_json_oracle.py
python3 tools/probe_lsp_workload.py \
  --measure "$PWD/build/lsp-workload-measure/build/exec/measure" \
  --output build/lsp-workload.json
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  python3 tools/probe_lsp_workload.py \
  --measure "$PWD/build/lsp-workload-measure/build/exec/measure" \
  --output build/lsp-workload-sanitized.json
```

The actual pinned Idris executable is
`/Users/odunadeboye/.local/state/pack/install/74b33730b6fea649b15e8d01ab099df9effcc7a0/idris2/bin/idris2`.
The probe has90-second execution deadlines and120-second check/emit/compile
bounds. A timeout raises/fails; it is never a represented parser rejection.
Normal and sanitizer builds run in distinct temporary directories; copied runtime
files only contain the existing profiler counter insertions. No C/Python runtime
parser is introduced. The tests check exact generated bytes, duplicate/id oracle,
UTF-16 edits, token/nesting/boundary labels, all64 committed evidence rows,
normal/sanitized equality and fail-closed observer deadlines/sanitizer detection.
Seven offline test groups and the existing eight JSON oracle tests passed.
Direct pinned `idris2 --mkdoc fibril.ipkg`, handbook generation/local-link checking
and all16 handbook tests also passed. An initial handbook generation invocation
failed because API reference artifacts had not yet been generated; it was not
counted as a pass. No full `make handbook`/unit-test prerequisite run is implied.

An initial offline UTF-16 test caught a hand-counted off-by-one coordinate (the
opening quote was omitted from the prefix count). That initial test failed; it
was corrected, corpus regenerated, and **both full matrices rerun** before the
committed evidence. Earlier observations on that draft were not edit-validity
passes. No final timeout or budget increase occurred. Broad repository, full
header/JSON-iteration matrices and editor integration were not rerun by this
lane; prior foundation acceptance and read-only inspection are not relabeled as
this task's executions.
