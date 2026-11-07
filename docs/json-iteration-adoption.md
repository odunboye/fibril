# JSON buffered binary iteration: 64-byte diagnostic milestone

This is **source-only diagnostic adoption**, not a production JSON library or a
4096-byte parser. Sources live in `tools/fixtures/json-iteration/`. The original
full/factored/shared fixtures and their historical evidence are unchanged. No
core, reducer, admission, native runtime, transport or primitive code changed.
Header integration is separate; independent admission does not prove composition.

## API and effect contract

```text
parseJSON       : (1 input : Bytes) -> JSONResult
parseJSONBinary : (1 input : Bytes) -> IO JSONResult
JSONResult = InvalidJSON | JSONTokens Bytes | JSONBoundedFailure
```

The new diagnostic's pure API still uses the original Nat fold. Its transition
and finalizer are shared with the new adapter, not copied into a second lexer.
The source-preservation test compares the entire lexical setup/transition and
finalizer verbatim against the accepted shared fixture. The old pure diagnostic
API in `json-admission/shared` is untouched. Neither pure API gains IO effects.

`parseJSONBinary` is explicitly **binary-effectful**, even though its callback
uses `primPure`. The caller supplies an already-buffered body. The parser contains
no read/write/flush/reject primitive. Invalid JSON (including an empty buffer) is
a data result inside IO, not transport EOF or fatal rejection. Exhaustion consumes
the returned linear state and returns the distinct `JSONBoundedFailure` result;
it never fabricates tokens or silently treats exhaustion as invalid syntax.

The allowance is byte length plus one (at most65): one transition per byte and a
final callback. A bad mode returns Done/Invalid immediately; Done with the finalizer
is possible only when no input remains, after trailing whitespace/garbage has been
processed. Whole-buffer strict UTF8 validation precedes scanning. The callback does
not stop just because a top-level value is recognized.

State WHNF alone is insufficient. The adapter reboxes rest/stack/tokens with the
existing Bytes-specific sharing operation. Hosted reduction materializes these
bytes; native boxes remain lazy, so existing `primBytesLengthIs Zero` inspections
demand **the same shared fields** before Continue. This bounds the deferred byte
chains in this adapter, not arbitrary field strictness or total heap usage.
The runner abstracts both state and result representations; local IO aliases avoid
re-expanding transparent wrappers. No new sharing/promotion facility is introduced.

## Policies and representation

Policies remain **64 input bytes / eight open containers**. Tokens and object
members are bounded by this byte cap (at most64 each), not separate512-token or
large-member counters. Raw string contents are at most62 source bytes; a number
lexeme is at most64. This is not the requested4096/eight/512 policy. No uniform
all-input runtime guarantee follows from the tested corpus.

Strings are validated **raw quoted escape lexemes**, not decoded Strings. Numbers
retain exact raw lexemes, including exponent spelling/negative zero. Tagged token
bytes preserve punctuation and duplicate-key order. Escaped surrogate pairs are
validated; lone surrogates, malformed escapes, raw controls/NUL, malformed UTF8 and
trailing input reject. Valid Unicode noncharacters are accepted. No grammar or
Unicode rule was removed to fit admission or CPU limits.

## Measured admission and execution

All four entries source-check under unchanged8192 initial nodes /200000
construction limits, with no exceptions or admission exemptions. Payload is
reported separately from nodes, as in the existing admission policy.

| Entry | Core nodes | Literal payload |
| --- | ---: | ---: |
| Pure API (`Parse.fib`) | 6205 | 892 |
| Binary API (`ParseBinary.fib`) | 7467 | 1037 |
| Pure reader (`PureRead65.fib`) | 6674 | 1005 |
| Binary diagnostic reader (`Read65.fib`) | 8002 | 1198 |

The original97 cases now produce **96 exact results plus one reader EOF on each
backend**, with zero budget blockers/mismatches. Those96 comprise63 valid token
transfers and33 invalid-data results. Previously hosted had70 matches/26 blockers
and native93/3; EOF is still not parser execution. The extended120-case matrix on
each backend has76 valid transfers,43 invalid-data results and one reader EOF,
zero budget rejections/mismatches/unexpected errors/deadlines. Direct empty input
is separately exercised successfully as InvalidJSON. These are corpus results,
**not full-grammar proof**.

| Native case | Steps | Peak pure depth | Arena payload | Callbacks |
| --- | ---: | ---: | ---: | ---: |
| 64 bytes whitespace + value | 43014 | 75 | 1343641 | 65 |
| Depth8 empty nesting | 19745 | 74 | 600152 | 17 |
| Depth9 denial | 11565 | 70 | 355845 | 10 |
| 63 tokens | 97136 | 81 | 2980861 | 64 |
| 64 tokens /64 bytes | 97768 | 81 | 2998705 | 65 |
| 64-byte ASCII string | 55660 | 70 | 1935876 | 65 |
| 64-byte UTF8 string | 67502 | 70 | 2500324 | 65 |
| Bad first byte +63 spaces | 2500 | 74 | 81921 | 2 |

All limits remain unchanged: hosted fuel/depth4096, checking depth512, native
100000 steps /512 pure depth /16MiB arena /4096 pending; transport reservations
are session-wide. The reader makes one capacity65 request and the caller writes
one result; native reservations are2 requests and65+output-length capacity.
The parser itself makes none. A no-output consumer of buffered `[1]` has4
callbacks,0 reads,0 writes and only the session's mandatory final-success flush.
Direct empty has1 callback/0 reads; test-only zero/one allowances return bounded
failure with0/1 callbacks. Interactive/resource gates reject the actual checked
term, and text run/default C emission also reject it.

### Cost isolation, not a replacement parser

On the same valid64-byte ASCII string, replacing **only in a private diagnostic
copy** the control predicate with False reduces native steps55660 to39786 and
arena payload1935876 to1230228 (same65 callbacks). The measured delta
is **15874 steps**, about28.5%. The production diagnostic retains control validation.
This isolates the cost of BytesIndex-to-unary-Nat / slice-based classification and
its wrappers, not exclusively Nat allocation. Removing it still leaves39786 steps
for only64 bytes. The63/64-token families almost exhaust100000 without using that
string predicate heavily. A cheap general byte comparison/classification operation
may help, but these measurements do **not** establish that one primitive would
make4096-byte JSON feasible. No new primitive is requested or implemented here.

Do not directly use a derived4096-byte length as the iteration count: its raw
count-decoder cost8194 already exceeds hosted4096. Larger policy needs a separate
decision and measured bounded-block scheduling, token assembly and classification
work. Nested loops do not reset native work/arena. Pure JSON folding remains a
separate operational problem. Header+JSON composition is not demonstrated.

## Validation and reproduction

Pin the existing compiler; all Fibril installation is private `build/test-prefix`.

```sh
I=/Users/odunadeboye/.local/state/pack/install/74b33730b6fea649b15e8d01ab099df9effcc7a0/idris2/bin/idris2
make -j8 json-iteration-test json-oracle-test IDRIS2="$I"
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' \
  make -j8 json-iteration-test IDRIS2="$I"
```

The adoption suite passes7 groups: exact source preservation, API/client size,
120-case hosted/emitted-native oracle matrix, explicit empty/exhaustion data,
no-parser-transport/admission gates, real binary stdio named subset, and classifier
cost isolation. ASan/UBSan covered every emitted executable in these groups:
120 matrix cases, direct-empty, zero/one exhaustion, no-output consumer,
classifier-bypass diagnostic; real-stdio subset `[1]`, duplicate object, valid
surrogate pair, raw NUL and64-byte padded number. No sanitizer diagnostics.
Ordinary and sanitized evidence rows are identical. The eight existing oracle
regressions pass, including overwritten invalid-surrogate values/nested objects.
Python JSON is reference-only, with `object_pairs_hook` retaining every duplicate
value for scalar validation. Runtime execution is Fibril source, not a Python/C
JSON implementation.

[Machine-readable observations](assets/evidence/json-iteration-adoption.json)
record categories, exact bytes, adapter/callback counters, node/payload and native
costs. The C harness is only an adapter around genuinely emitted source. Observer
copies insert counters only, never change evaluator decisions or budgets. All
process commands have foreground deadlines; deadlines fail, not count as bounded
rejection. Earlier draft checks exceeded8192, and early harness runs failed on
typing/CLI/instrumentation assertions; these are not counted as passes. The final
normal and sanitizer7-group runs passed; the worker did not run a cold full-repository
suite for that milestone.

Independent review accepted this scoped diagnostic. The parent separately ran the
oracle8 and direct source-preservation check, recalculated all254 recorded rows
against normal/sanitized build evidence and current oracle, then reran all7 groups
normally and with ASan/UBSan on the integration branch. The combined parent
`make -j8 test editor-test handbook` invocation also passed after integration.
These are acceptance checks for the diagnostic, not a production/4096-byte or
composition claim.
