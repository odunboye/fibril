# Experimental native pure pairs

Native `PairValue` and `PairCase` lowering now works in **Preflight,
Interactive, Resources and Binary**, with recursive emission retaining the
caller's mode. This is pure-data support, not new effect permission.

The only compiler change is in `src/Fibril/Driver/Native/Emit.idr`:

- Pair annotations still expose `Sigma` using the existing bounded weak-head
  reduction. The two quantity flags still drive `f_pair` field erasure.
- Pair fields remain thunks; erased fields have no runtime thunk. Elimination
  still applies the branch to those fields without eagerly forcing them.
- Original whole-syntax admission, runtime type checking, node/payload limits,
  annotation reduction fuel and runtime budgets are unchanged. No normalization
  or erasure is moved ahead of admission.
- Binary/nonbinary separation, scoped-resource operations and runtime file
  references retain their existing gates. Generating a pair does not enable
  `WithInputFile`, `ReadInputFile`, `FileHandleValue`, or console reads in another
  mode. Runtime source, byte views, arenas and session lifetimes are untouched.

This is an experimental checked-core-to-C subset, not a verified backend or a
proof of QTT preservation, world-token discipline, exactly-once behavior, or
exception safety.

## Focused evidence

`tools/test_native_pairs.py` separates actual source from raw fixtures:

- `examples/modules/native-pairs/{Pairs,Main,Binary}.fib`: checked nested records
  with erased, linear and unrestricted fields; demanded fields and duplicated
  unrestricted suffixes agree hosted/native in Preflight and Binary.
- Existing `examples/modules/records/{Main,Patterns}.fib`: dependent record
  packages with an erased type field agree hosted/native.
- `examples/modules/native-pairs/Input.fib`: a borrowed binary input slice passes
  through an erased/linear pair and is written correctly for EOF, short input,
  NUL, invalid UTF-8 and ordinary bytes.
- Generated checked source: oversized erased and unused fields, and a dormant
  branch, are not forced in either Preflight or Binary. Erased use, linear
  duplication, linear dropping and wrong field types are rejected by source
  checking. Checked erased IO fields (including a dormant forbidden branch)
  cannot hide forbidden capabilities or permit prefix output.
- `test/src/Tests/PairEmission.idr`: raw-core fixtures cover all nine field
  quantity combinations in all four modes (36 emitted/compiled/executed entries).
  Raw, intentionally sometimes ill-typed wrappers assert exact whole-syntax
  rejection diagnostics before checking, including pair annotations, erased
  fields, erased Sigma domains, motives and dormant branches. Resources still
  rejects raw file references; old modes still reject scoped resources.
- A separate raw C poison-callback fixture checks field/branch laziness. This is
  runtime evidence, **not** source typing evidence.

The Interactive CLI only accepts standalone sources, not record modules; its
pair lowering is exercised through the raw checked-core fixtures. No CLI or
source-loading expansion is included.

Run after `make -j8 build` (set `IDRIS2` to the curated compiler executable rather
than a cwd-sensitive Pack shim when necessary):

```sh
export IDRIS2="$(pack --log-level=silence app-path idris2 | tail -n 1)"
python3 tools/test_native_pairs.py
FIBRIL_PAIR_SANITIZE=1 python3 tools/test_native_pairs.py
make -j8 native-pair-test
```

The raw observer builds in a private temporary directory. The unit-test target
stages only into this worktree's `build/test-prefix`; no shared Fibril installation
or Pack cache removal is needed. The suite is also registered in `test` and
`native-test`. The previous wider-data native rejection test now checks successful
hosted/native agreement for its dependent pair payload.

## Validation accounting and recovery

These results use the curated compiler executable as `IDRIS2`; package
installation was confined to `build/test-prefix`.

| Command | Recorded outcome |
| --- | --- |
| `make -j8 build` | Exit 0; rebuilt the changed emitter and executable. |
| `make -j8 unit-test` | Exit 0; worktree-local unit/property suite passed (`/tmp/fibril-pair-unit-final.{log,exit}`). |
| `make -j8 test editor-test handbook` | **Exit 2, not a full-invocation pass.** The handbook initially rejected the unregistered new page. The remaining recipes completed successfully: 163 CLI, 19 native, 8 pair, 7 byte-native, 13 binary-source, 1 binary-native bridge, 9 scalability, 6 numeric, 14 framing, 9 IO CLI and 7 editor tests (`/tmp/fibril-pairs-full-final.{log,exit}`). |
| `make -j8 -o unit-test handbook` | After registering the page in `docs/book.json`, exit 0: handbook built, local links checked and 16 tests passed. `-o unit-test` reused the already successful unit/build prerequisite without rebuilding the executable during CLI tests (`/tmp/fibril-pair-handbook-verified.{log,exit}`). |
| `make -j8 io-resource-runtime-test io-resource-emitter-test` | Exit 0: 25 runtime tests and 29 checked hosted/native comparisons (`/tmp/fibril-pair-resources-final.{log,exit}`). |
| `FIBRIL_PAIR_SANITIZE=1 python3 tools/test_native_pairs.py` | Exit 0: all 8 tests passed with ASan+UBSan, including 36 emitted raw-core entries (`/tmp/fibril-pair-sanitizers-verified.{log,exit}`). |

`Tests.PairEmission` is not an orphan unit module: the Python suite writes an
observer importing it, evaluates every exported admission check, emits
`pairEntry` for all quantity/mode combinations, then compiles and executes all
36 resulting C files. It is exercised by the pair suite registered in both
`test` and `native-test`.

Preliminary validation failures are not counted as passes: early fixture and
Pack-shim invocations failed; a preliminary combined suite was interrupted after
a concurrent rebuild caused transient executable permission errors; a separate
10-second build-command deadline expired. Subsequent build/staging finished
before the stable combined suite above began. Its exit 2 is specifically the
historical missing-page registration failure, not a timeout or a passing make
invocation; the corrected handbook target was validated separately.

The original worker session then reached its 1800000 ms orchestration timeout
while polling after the completed suite. A single scoped recovery inspected the
saved exit files/logs and the staged diff, confirmed that the Idris pair fixture
is exercised, and recorded this accounting before committing. No full suites
were rerun during recovery, and no timeout is treated as a test pass. Local
`/tmp` log paths identify this run's evidence, not permanent repository artifacts.

## External JSON checkpoint, not a parser delivery

Read-only fixture provenance:
`../fibril-protocol-json`, commit
`6301779ad47cb0efdd03904f9a8895175bc1e2bb`,
`tools/fixtures/json-admission/scalar/Main.fib`.

Using this worktree's compiler with explicit external source paths, input hex
`31` (`1`) checks and emits native binary C. Hosted, native and ASan+UBSan native
execution each return exit 0, empty stderr and output hex **`233100`** (`#1` plus
NUL). Native emission is 442775 bytes. This removes the scalar fixture's pair
lowering blocker; it does not establish its complete scalar grammar.

The full parser body's previously measured 12170 nodes still exceed the unchanged
8192-node admission. Rechecking native emission of `full/Main.fib` with this
emitter returns exit 1, no stdout and `Native core admission exceeds 8192 nodes`.
No full grammar, 4096-byte parser, Unicode/boundary matrix,
static-sharing solution or runtime scaling guarantee is delivered here. Neither
external JSON source nor its original blocker document was edited.

Reproduce from this worktree without copying or changing the external fixture:

```sh
JSON_ROOT="$(cd ../fibril-protocol-json/tools/fixtures/json-admission/scalar && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
build/exec/fibril check --source-dir "$JSON_ROOT" "$JSON_ROOT/Main.fib"
printf 1 | build/exec/fibril run-binary --source-dir "$JSON_ROOT" "$JSON_ROOT/Main.fib" | od -An -tx1
build/exec/fibril emit-c-binary --source-dir "$JSON_ROOT" "$JSON_ROOT/Main.fib" > "$TMP/scalar.c"
cc -std=c11 -Wall -Wextra -Werror -fsanitize=address,undefined -fno-omit-frame-pointer \
  -I runtime/native "$TMP/scalar.c" runtime/native/fibril_binary_runtime.c -o "$TMP/scalar"
printf 1 | "$TMP/scalar" | od -An -tx1
```
