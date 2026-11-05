# Console IO execution contract

Scope: current stdout-only hosted and native paths on `feature/qtt`.
This is an observable implementation contract, not a preservation proof.

## Shared behavior

- Checking, conversion and normalization do not execute host writes.
- Execution requires a checked closed `IO Unit` entry at the driver boundary.
  The native C runtime itself is trusted code, not a source type checker.
- Prepare the entire admitted write plan and its Unit result before output.
  Planning failure emits no prefix. Host failure during execution can leave a
  prefix; no rollback, durable-storage or crash-recovery guarantee is made.
- Perform writes in bind order. Each request writes its text followed by one
  newline. Bind supplies the earlier action's result to its continuation.
- Admit at most 64 writes. Hosted and native resource/reduction budgets otherwise
  differ; matching admission for every well-typed program is not promised.
- Stop on represented write failure. After successful sequencing, including an
  empty plan, flush stdout and report flush failure. Do not retry writes or
  explicitly perform the final flush after a reported write failure.
- Descriptions can be reusable when bound unrestrictedly. This contract makes no
  exactly-once claim for external effects under crashes, nor a world-token claim.

## Backend boundaries

The hosted flush adapter calls C `fflush` and has been exercised on Chez. This
is not an implementation of Node flushing. Native output uses explicit UTF-8
byte lengths. The native emitter accepts a smaller computational language than
the hosted runner; see [native-c.md](native-c.md).

Source-level error values, input, handles and interactive continuations are not
covered. Adding them requires revisiting preflight planning, encoding/EOF rules,
capability ownership and cleanup after partial effects.

## Evidence

Run `make -j8 io-test`. Its four suites build in independent temporary
directories and can run concurrently:

- 179 hosted core IO/argument/sequence/script/input/resource checks, plus a real flush smoke
  test and three checked-core stdin smoke tests (Unicode CRLF, EOF and input
  length failure);
- 17 direct C runtime tests for output planning and the separate interactive
  runtime, including UTF-8, EOF, read failure, length/request limits, prompt
  visibility, late-result output suppression and broken-pipe flush failure;
- seven source-to-C examples whose compiled stdout matches the hosted plan,
  covering sequencing, helpers, do lets/results, computed strings and IO map;
- seven source-level hosted/native interactive file-driver comparisons, described separately
  in [io-native-input.md](io-native-input.md), not governed by preflight semantics.

The hosted checks include rejecting an over-budget write before normalizing its
expensive text. The broken-pipe harness ignores SIGPIPE so stdio can return its
error; production signal handling is unchanged, and default signal termination
is not promised to become a represented error.

The direct C fixtures bypass elaboration and emission and intentionally include
an invalid result to exercise defensive runtime checks. They do not establish
that such a result can pass source checking. The separate source-to-C tests exercise checked emission through
`Driver.Native.Emit`, extracted unchanged from `Driver.Native` (which re-exports
it). They avoid project loading. The full CLI/package/module suites also pass;
see [build validation](io-build-validation.md) for the separate full-suite scope.
