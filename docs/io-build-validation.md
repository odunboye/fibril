# IO build validation boundary

The focused suites run independently in temporary directories:

```sh
make -j8 io-test
# If the package-manager launcher is unavailable:
make -j8 io-test IDRIS2=/path/to/installed/idris2
```

This runs 168 hosted checks, real flush/stdin smoke tests, 17 direct C runtime
tests, seven output-only compiled examples and seven interactive source-level
hosted/native comparisons. It checks the standalone input file drivers but not
the complete CLI binary's argument dispatch or project/package paths.

## Full-CLI blocker observed locally

`make -j8 build` timed out inside the package/compiler path. A bounded direct
compiler diagnostic of the full Main dependency graph was CPU-active rather
than sleeping; one early sample showed approximately 5.8 GB resident memory and
predominantly garbage collection. The diagnostic was stopped rather than left
consuming resources. This observation does not identify the responsible module
or establish a regression introduced by IO.

A minimal YAML import checks when its transitive installed packages are supplied.
Therefore calling the full-CLI failure simply a YAML bug is not justified. The
full dependency graph still needs a reproducible baseline comparison and module
bisection before attributing the allocation behavior. Shared package state and
other sessions' builds were not changed to work around it.

Until a complete CLI build and dispatch tests pass, distinguish implemented and
tested file-driver behavior from the unvalidated final CLI integration. Focused
suite success is not a substitute for full project tests, property tests or
quantitative preservation proofs.
