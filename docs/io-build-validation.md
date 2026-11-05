# IO build validation

## Passing commands

```sh
make -j8 build
make -j8 io-cli-test
make -j8 test
make -j8 io-test
```

The current checked-resource-emission revision passes `make -j8 build`,
`make -j8 test` and the complete focused `make -j8 io-test` separately. The full
focused IO target also passes with address/undefined-behavior sanitizers enabled
through CC. Earlier aggregate `test io-test` runs hit 300/600-second deadlines
without a reported test failure; those timed-out invocations are not passes.

The focused suites accept `IDRIS2=/path/to/installed/idris2` and build independently
in temporary directories, allowing parallel execution.

Validation includes:

- deterministic bootstrap regressions;
- 27 property groups, each sampling 100 cases;
- 108 existing full-CLI tests, including project creation and module/package paths;
- 12 existing native-emitter tests;
- 9 interactive tests against the actual built CLI, including emitted C;
- 258 focused hosted checks plus constructor-opacity and flush/stdin smoke tests;
- 19 direct console-native runtime tests and 25 resource-native runtime tests;
- seven compiled output-only examples and ten interactive source-level comparisons;
- 25 checked-core resource hosted/native comparisons, including real process
  failure status, input-byte errors, ownership threading and visible prefixes;
- all native portions of the focused IO target pass with address/undefined-behavior
  sanitizers, including generated resource programs.

## Resolved build stall

Earlier full builds stalled and a sampled compiler process showed heavy garbage
collection and approximately 5.8 GB resident memory. Terminal logging localized
the stall to `Project.New`, before the IO CLI modules. Its private option parser
matched several Boolean/Maybe state arguments in clause heads. Rewriting it to
dispatch on arguments first and inspect state inside the branches removed the
observed stall; existing CLI/project tests pass with unchanged option messages.

A minimal YAML import checks with its transitive packages, so the earlier
attribution to YAML was not supported. Once compilation progressed, it exposed
an emitter-refactoring regression: `Driver.Native` lacked an explicit import of
`Core.Term`. That import is restored, and the complete Main module and executable
now build. The experimental resource driver is also kept in Main's import
closure so application-package builds include the library interfaces needed by
the installed test dependency; no resource CLI command is exposed by that import.
No other worktree was changed for these fixes.

These tests establish observed behavior, not quantitative preservation, a verified
backend, an all-input equivalence theorem or exception-safe linear resource ownership.
