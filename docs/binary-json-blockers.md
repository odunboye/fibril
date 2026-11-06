# Pure JSON source admission checkpoint (blocked)

**Not an implemented JSON library.** The diagnostic sources in
`tools/fixtures/json-admission/` are deliberately outside normal example/test
registration. No production JSON API is exported by this milestone. Per supervisor
direction, work stopped after measuring the full prototype and one reduced slice;
no core/runtime changes or budget increases were made.

## Reproduced observations

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
