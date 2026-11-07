# Protocol foundations integration checkpoint

This branch combines independently reviewed native pure-pair lowering and
source-only JSON state sharing. It does **not** deliver generalized headers,
production JSON, JSON-RPC or a server. The canonical 4 KiB framer is unchanged.
Main and the separate LSP worktree are not merged or modified.

## Reviewed components

- Native pairs (`1b84e16`, integrated as `c4b7220`): ordinary pair/record lowering
  retains caller mode, field erasure and laziness. Resource/binary gates and all
  budgets remain unchanged. Independent source/artifact review found no corrective
  production issue. It did not independently execute the worker's tests.
- State sharing (`d530338`, integrated as `258a0d3`): erased state abstraction and
  one lexical `equalString` binding reduce the diagnostic parser from 12170 to
  5972 core nodes; its wrapper is 6479, below the unchanged 8192 cap. Source-
  preservation checks pass. This is not proof of runtime grammar coverage.
- Iteration: the design checkpoint (`2ebb7b3`, integrated as `bcc7772`) is now
  followed by implementation `d99022e`/`04088eb`, count safety `3b7edb8` and
  payload tests `aa9741e`. Independent reviews accepted the reducer/count policy
  and the typing/admission/runtime changes; distinct-payload lifetime coverage
  closed the follow-up finding. See [bounded binary iteration](bounded-binary-iteration.md).
  Ordinary reducers retain their unmetered semantics. Count decoding charges
  nested canonical traversal and unary construction before allocation, not
  arbitrary CPU/heap activity. Sanitizer coverage is named by tested subset.

The pair worker's combined regression invocation exited **2**, not success,
following an early handbook-registration failure. Individual later test outcomes
and the corrected isolated handbook pass are documented in
[native pure pairs](native-pure-pairs.md). Its 30-minute agent timeout is not a
validation pass. Recovery finalized the existing changes rather than silently
rerunning the entire workflow or switching tools.

## Oracle correction

Independent review found that `json.loads`' default dictionary conversion could
hide an invalid surrogate in an overwritten duplicate-key value. The observation
oracle now uses a distinct object-member list and validates **all** keys and
values, including nested overwritten objects. Arrays stay ordinary arrays.

`tools/test_json_oracle.py` covers invalid duplicate values in both orders,
nested objects/arrays, invalid keys, valid duplicate ordering, valid surrogate
pairs, malformed JSON/UTF-8, source preservation and outcome accounting.
This fixes the diagnostic oracle, not a demonstrated Fibril parser bug. The
historical 94-case evidence file is retained as historical evidence; its cases
did not include the newly found defect.

## Combined hosted/native observations

`tools/observe_json_combined.py` emits the actual shared `Read65.fib` fixture and
compiles it with the pair-enabled backend, then runs the original 94 cases plus
three duplicate-surrogate regressions. The parser is still a **64-byte diagnostic**;
the reader accepts up to 65 to probe denial. Raw quoted strings/numeric lexemes
are tokens, not decoded AST strings. No source parser is implemented in Python/C.

Parent validation used compiler `fibril-native-pairs/build/exec/fibril` from
`1b84e16` (same production emitter now integrated here), explicit integration
fixture paths and this branch's runtime sources. Native compilation used
ASan/UBSan. Of 97 observations per backend:

| Backend | Exact matches | Runtime-budget blockers | Reader EOF | Mismatch / unexpected / timeout |
| --- | ---: | ---: | ---: | ---: |
| Hosted | 70 | 26 | 1 | 0 |
| Native | 93 | 3 | 1 | 0 |

Native blockers were 63/64-byte whitespace-plus-value inputs and the 63-token
case. Hosted blockers include nonempty containers and some escapes. Budget
blockers and the reader's empty-input EOF are **not successful parser executions**.
Repeating the same matrix with this integration worktree's freshly built
compiler produced the identical counts. No full grammar, depth/token boundary
guarantee or 4096-byte JSON support is claimed. Sanitizer-clean represented failures are not equivalence successes.

```sh
make -j8 json-oracle-test
make -j8 json-sharing-probe
CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer' make -j8 json-sharing-probe
```

The probe honors `FIBRIL`/`CC`, isolates temporary artifacts, and fails on wrong
output, unexpected diagnostics, sanitizer errors or deadlines. Existing budget
failures remain recorded observations, not golden tests that must fail forever.
Integration build and unit/property phase passed. The eight oracle tests, three
probe-tool tests and eight pair tests passed. Handbook generation/tests passed
(16 tests) after registering the diagnostic pages and relocating the unchanged
historical evidence JSON into `docs/assets/evidence/`. The earlier handbook
invocation failed on that missing static asset and is not counted as success.
A default compiler-wrapper invocation also failed to resolve Pack's compiler;
the pinned existing Idris2 path succeeded without modifying any shared install.
That initial pair/state checkpoint used split validation. After iteration was
reviewed and integrated, the parent combined `make -j8 test editor-test handbook`
invocation passed, as did315 hosted IO checks and the targeted sanitizer/differential
runs. See [iteration acceptance](bounded-binary-iteration.md#parent-acceptance-on-the-foundations-branch)
for exact counts, coverage and limits; the earlier failed invocations are not
retroactively counted as passes.

No runner limits were raised. Bounded early-completion iteration is now available
on this isolated foundations branch with explicit state/result and work contracts;
this is not an implicit natRec strictness change. Header/JSON consumers have not
been rewritten to use it. Generalized headers, JSON runtime limits and subsequent
JSON-RPC integration remain separate work.
