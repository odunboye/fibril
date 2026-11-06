# QTT integration validation

Integration parents: `master` at `3b1e3dd` (recursive data and import/navigation
integration) and `feature/qtt` at `ab288bc` (checked resource IO).

The merge was resolved and tested in the separate `integration/qtt` worktree,
without editing either parent's working tree during integration.

## Resolution

- Preserve both recursive and resource constructors in core traversal, typing,
  usage analysis, substitution proofs and elaboration helpers.
- Retain the extracted `Driver.Native.Emit` module and port main's Nat,
  runtime-predecessor Nat, unary recursive-data and sequence lowering into all
  emitter modes. File/project adapters remain in `Driver.Native`.
- Combine recursive fold thunks with the native file registry and resource tags.
- Extend `containsFileReference` through every recursive constructor, including
  annotations and motives. Twelve added regressions check admission rejection
  before type checking, plus absence of false positives on reference-free trees.
- Add four checked hosted/native comparisons evaluating the fold families inside
  acquired file scopes. Existing output/console-only resource gates are retained.
- Make editor tests depend on the built CLI, avoiding a parallel linker race.

## Passing validation

```sh
make -j8 build
make -j8 test editor-test
make -j8 io-test IDRIS2=/path/to/idris2 \
  CC='cc -fsanitize=address,undefined -fno-omit-frame-pointer'
```

Observed: unit/property checks; 161 CLI tests; 19 native-emitter tests;
9 interactive CLI tests; 7 editor tests; 285 focused hosted checks; constructor
opacity and stdin smoke tests; 19 console-native and 25 resource-native runtime
tests; 7 output examples; 10 source-interactive comparisons; and 29 checked-core
resource comparisons. Native portions of the focused IO target ran under
AddressSanitizer and UndefinedBehaviorSanitizer.

An earlier parallel test/editor invocation failed because the editor suite ran
while the executable was being linked. The dependency fix and rerun passed;
the failed invocation is not reported as a pass. One new fold fixture initially
used an unrestricted predecessor where NatRec requires erasure; checking rejected
it, and the corrected fixture is included in the passing results.

This remains finite evidence, not quantitative preservation or a verified backend.
Source file primitives remain disabled. The untracked greeting example from the
QTT worktree is not part of the merge.
