# Pure JSON diagnostic: source sharing admitted, runtime still blocked

**Not an implemented JSON library.** The diagnostic sources in
`tools/fixtures/json-admission/` remain outside normal example/test registration.
No production JSON API, compiler/runtime change, admission exemption or budget
increase is introduced. The original full and scalar fixtures remain unchanged.

## Source-only state-sharing checkpoint (base `6301779`)

The first typed abstraction **checks**, but alone does not fit admission. The
approved follow-up lexical-sharing sweep then fits both the single full parser
and its identical thin IO wrapper under the unchanged **8192 initial nodes**:

| Variant / checked entry | Core nodes | Literal payload | Node delta from preceding variant |
| --- | ---: | ---: | ---: |
| Original `full/Parse.fib` | 12170 | 892 | — |
| State-abstract `factored/Parse.fib` | 10914 | 916 | -1256 |
| State + comparison sharing `shared/Parse.fib` | **5972** | **916** | **-4942** |
| Original `full/Main.fib` | 12677 | 940 | — |
| State-abstract `factored/Main.fib` | 11421 | 964 | -1256 |
| State + comparison sharing `shared/Main.fib` | **6479** | **964** | **-4942** |
| `shared/Read65.fib` diagnostic boundary reader | 6397 | 1029 | Different reader, not a size comparison |

Total reduction is **6198 nodes** for both like-for-like entries. The state-only
variant is retained as an independent checkpoint, not presented as admission
success. All entries source-check. `Main.fib` is byte-identical across the three
full-grammar variants, including its diagnostic 16-byte read.

### Typed kernel and lexical sharing

The private kernel consistently abstracts the state representation, constructor,
eliminator, state annotations and Nat-fold motive:

```fibril
parseJSONKernel : (0 S : Type) ->
  (scanning : (rest : Bytes) -> (stack : Bytes) -> (mode : String) -> (tokens : Bytes) -> S) ->
  (eliminate : (0 R : Type) -> (1 state : S) ->
    (fields : (rest : Bytes) -> (stack : Bytes) -> (mode : String) -> (tokens : Bytes) -> R) -> R) ->
  (1 input : Bytes) -> JSONResult
```

`parseJSON` instantiates this once with `Scan`, `Scanning` and a wrapper around
`consumeScan (\(0 self : Scan) => R)`. The eliminator result is nondependent;
concrete record types do not leak into the abstract kernel's motives. This is
not a local definitional type-alias assumption.

Inspection found **166** references to the transparent Prelude `equalString`
wrapper around transparent `primStringEqual`, versus 72 `orBool` and 16
`primBytesAppend` references. The second variant binds the real comparison once:

```fibril
let (sameText : (1 left : String) -> (1 right : String) -> Bool) = equalString in
```

Only comparison references change to `sameText`; no Bool/Bytes aliases or further
sweeps were needed. A source-preservation assertion reconstructs each kernel
from the original with only these approved binding/reference substitutions and
checks exact body text equality. No grammar, token, stack or Unicode-state fixes
are hidden in the experiment.

### Hosted execution and bounded independent comparison

`python3 tools/observe_json_state_sharing.py` completed **94** bounded cases:
**70 executed exact matches**, **23 reduction-budget blockers**, **1 wrapper EOF**,
**0 output/grammar mismatches** and **0 unexpected failures**. Exit zero means
observation completed, **not** a full-parser correctness pass. Its JSON summary
explicitly says `validation: blocked`. Python `json.loads` supplies grammar
acceptance; independent lexical tokenization preserves punctuation, raw quoted
strings, raw numbers and duplicate-key order. Python's acceptance of escaped lone
surrogates is reported separately from the prototype's scalar-Unicode policy.

Measured examples (exit 0, empty stderr):

| Input | Exact output hex |
| --- | --- |
| `1` | `233100` |
| `[]` | `5b5d` |
| `{}` | `7b7d` |
| `"a"` | `5322612200` |
| `true` / `false` / `null` | `54` / `46` / `4e` |
| `1.0` / `1e2` | `23312e3000` / `2331653200` |

Raw UTF-8 `"é"` and `"𝄞"`, the `"\n"` escape, malformed numeric forms,
invalid UTF-8, control characters and several structural rejections execute as
expected. **`[1]`, `[[]]`, `{"a":1}`, duplicate-key objects, `"\u0041"`, and
paired-surrogate escapes exhaust the unchanged binary reduction budget.** They
are neither grammar passes nor observed grammar mismatches. Nonempty containers,
key/value/colon/comma success, duplicate preservation, full escape coverage and
surrogate pairing remain operationally unvalidated. The empty stdin case takes
the reader's EOF rejection path, not the parser's empty-input branch.

### Actual limits, not targets

The parser's **source policies remain 64 input bytes and eight open containers**;
4096 bytes / eight depth / 512 tokens remain undelivered. `Read65.fib` supplies at
most 65 bytes to expose the size guard without the original reader's 16-byte
truncation. It is not EOF framing and is only exercised with inputs at most 65
bytes. A 65-byte valid JSON value rejects as NUL (exit 0); 63- and 64-byte
whitespace-padded values exhaust reduction. No operational 64-byte guarantee is
claimed.

Exact measured families under current hosted fuel (not general maxima):

- Repeated `1` number lexemes: lengths 1–6 succeed, 7–8 exhaust reduction.
- ASCII strings: total lengths 2–12 succeed (0–10 content bytes), 13 exhausts.
  The longest successful value in this corpus is 12 bytes.
- Nested empty arrays: depth 1 succeeds; depths 2, 8 and 9 exhaust reduction.
  The eight-depth acceptance and ninth-depth rejection are not runtime-validated.
- Empty array's two tokens succeed; `[0]` (three tokens), `[0,0]` (five), and a
  63-token array exhaust reduction. No 64- or 512-token operational cap is proven.

There is no uniform measured input/depth/token cap for this grammar-dependent
reduction cost. Scaling repeated slices and Nat folds is still an open runtime
problem. Native emission for both admitted shared readers exits 1 with
`C backend does not support this computational core construct`; pair support is
a separate pending lane, not a pass or an emitter change in this branch.

### Reproduction and validation accounting

```sh
make -j8 build
# Resolve the real compiler, not Pack's cwd-sensitive idris2 shim:
IDRIS2_REAL="$(pack --log-level=silence app-path idris2 | tail -n 1)"
make -j8 unit-test IDRIS2="$IDRIS2_REAL"
python3 tools/observe_json_admission.py
python3 tools/observe_json_state_sharing.py
```

The admission observer defaults to the real compiler resolved in the worktree,
so its private `IDRIS2_PACKAGE_PATH` survives instead of being reset by Pack's
shim. It measures against `build/test-prefix`; `--variant shared` selects only
the final variant. No shared install, cache cleanup or unrelated process kill
was used. Pack's temporary-directory warnings were left alone.

- `make -j8 build`: exit 0.
- Initial shell attempt to pass the resolved compiler into Make failed because
  Pack printed a warning into the shell substitution; not a test pass.
- `make -j8 unit-test IDRIS2=<real compiler>`: command-tool timeout at 300 seconds,
  **not a suite pass**. The already-running child compilation was left to finish.
- Afterwards, direct `test/build/exec/fibril-tests`: exit 0 (existing unit suite,
  not JSON semantics).
- Final admission observer: exit 0; exact metrics and child rejection statuses
  above, reproduced using the private local library.
- Hosted observer: exit 0, with explicit blocked verdict as detailed above.
- `python3 -m py_compile` for both observers: exit 0.

Machine-readable case-level evidence is in
[`json-state-sharing-evidence.json`](json-state-sharing-evidence.json).
No native executable, sanitizer result, full grammar-equivalence pass, production
API or 4096-byte runtime feasibility is claimed. Parent review and the separate
pair lane are required before any integration beyond this source-only milestone.

## Historical original checkpoint: reproduced observations

Measured against baseline `0efe064` with the worktree-built compiler and an
observer importing the worktree-local library (`build/test-prefix`):

| Checked entry | Core nodes | Literal payload | Hosted binary | Native binary emission |
| --- | ---: | ---: | --- | --- |
| `full/Parse.fib` (pure function) | 12170 | 892 | Not an IO entry | Not an IO entry |
| `full/Main.fib` (one parser use) | 12677 | 940 | Admission rejection | Admission rejection |
| `scalar/Main.fib` | 6482 | 920 | Input `1` succeeds | Unsupported core construct |

All three module graphs pass `check`. The full **single parser body** already
exceeds the unchanged 8192-node initial admission. The small binary wrapper adds
507 nodes; duplication by multiple client calls is not the cause.

Exact full-entry diagnostics (exit 1, no stdout):

```text
Binary entry rejects non-binary IO/references or exceeds admission limits
Native core admission exceeds 8192 nodes
```

The reduced slice parses only numbers, booleans and null. Its one measured hosted
execution is input hex `31` (`1`), exit 0, output hex **`233100`** (`#1` then NUL),
with empty stderr. Native emission exits 1, no stdout:

```text
C backend does not support this computational core construct
```

The source's multi-field `Scan` record uses pairs and pair elimination. Inspection
of `src/Fibril/Driver/Native/Emit.idr` shows `PairCase` and `PairValue` generation
restricted to **Resources**, not Binary. This is a second, independent obstacle;
fixing the reduced slice would not establish admission of the full parser. No
permission to widen these modes was granted, and those files remain untouched.
A discarded local-type-alias optimization also failed source branch conversion;
it is not a successful measurement or a claimed solution.

## Prototype interface and representation (not production)

The full diagnostic module checks this source signature:

```fibril
parseJSON : (1 input : Bytes) -> JSONResult
-- InvalidJSON | JSONTokens (1 tokens : Bytes)
```

It attempts a pure byte scan for objects, arrays, strings, numbers, booleans and
null, whitespace handling, strict UTF-8 conversion and trailing-data rejection.
There is no IO or `primRejectBytes` inside either parser. **Checking the source
is not evidence that these grammar decisions execute correctly.**

The proposed successful representation is source-order tagged token bytes:

- `{`, `}`, `[`, `]`, `:`, `,` are their own one-byte tokens.
- `T`, `F`, `N` denote true, false, null.
- `#`, raw number lexeme, NUL form one number token. No floating-point conversion.
- `S`, raw **quoted** JSON string lexeme, NUL form one string token. This is not
  decoded text. Unescaping is not implemented. The prototype contains escape,
  control and paired-surrogate validation states, but they remain unexecuted.

Whitespace is omitted, so the encoding aims to preserve value/lexeme structure,
not byte-for-byte source formatting. Object-key tokens stay in order; the intended
policy is **preserve duplicate keys**, with no map overwrite or key normalization.
The scalar slice exports `parseJSONScalar : (1 input : Bytes) -> JSONScalarResult`
with `InvalidScalar | ScalarTokens Bytes`, using only `#`, `T`, `F`, `N` tokens.

Both sources currently contain a **prototype-only 64-byte cap**, not the requested
4096-byte API. The full source encodes at most eight open containers. Input size
would imply at most 64 tokens, array elements or object members; raw string lexemes
and number lexemes would also be bounded by the input cap (at most 62 bytes
between string quotes). These are source policies, **not measured operational
limits**: no boundary matrix ran. The diagnostic binary clients read at most 16
bytes and do not check for further input; they are not framing or JSON clients.
The cap was chosen for the initial scan experiment before runtime measurements;
static admission blocked it first. It is not a measured substitute for 4096.

The scan uses Nat folds and repeated byte slices. Scaling these to 4096 has not
been demonstrated; no runtime work, depth, arena or heap bound is claimed.
The requested 4096-byte / eight-depth / 512-token hosted-and-native parser remains
**undelivered**.

## Reproduce without shared installations

```sh
make -j8 build
# Uses build/test-prefix, never a shared Fibril installation:
make -j8 unit-test
python3 tools/observe_json_admission.py
```

The observer requires the local library staged by `tools/test_units.py`, builds
`Measure.idr` in its own temporary directory, and prints JSON observations of
`checkProject`, `coreNodes`, `payloadSize`, `check`, `run-binary` and
`emit-c-binary`. `FIBRIL`, `PACK` and `IDRIS2` can select tools explicitly. It does
not assert that failures must persist: it is an observation tool, not a golden
failure regression suite. Nonzero child statuses are printed, not interpreted
as equivalence successes. Compiler build failure or deadlines abort observation.

Individual execution commands (from repository root):

```sh
ROOT=tools/fixtures/json-admission/full
build/exec/fibril check --source-dir "$ROOT" "$ROOT/Parse.fib"
printf 1 | build/exec/fibril run-binary --source-dir "$ROOT" "$ROOT/Main.fib"
build/exec/fibril emit-c-binary --source-dir "$ROOT" "$ROOT/Main.fib"
ROOT=tools/fixtures/json-admission/scalar
printf 1 | build/exec/fibril run-binary --source-dir "$ROOT" "$ROOT/Main.fib"
build/exec/fibril emit-c-binary --source-dir "$ROOT" "$ROOT/Main.fib"
```

## Validation accounting

- `make -j8 build`: exit 0.
- `make -j8 unit-test`: the invocation hit the command tool's 300-second deadline
  after logging compilation of `fibril-tests`. **Not recorded as a suite pass.**
  Its library installation was confined to this worktree's `build/test-prefix`.
- Separately, `test/build/exec/fibril-tests > /tmp/json-unit-results.log 2>&1`:
  exit 0. This executable was produced by the preceding local unit-test build;
  it exercises the existing suite, not JSON parser semantics.
- `python3 tools/observe_json_admission.py`: exit 0; reproduces the statuses and
  measurements above against the worktree-local library/compiler.
- No native JSON executable could be emitted, so no native execution or sanitizer
  result exists. No independent Python JSON differential, grammar/Unicode matrix,
  depth/token/byte boundary validation or full-parser AST projections are claimed.

Next work requires a separately approved direction for static source sharing and
source-supported state representation. Raising admission alone would neither
resolve the Binary pair restriction nor demonstrate 4096-byte runtime feasibility.
