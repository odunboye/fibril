# 6. Console programs and projects

[Previous](05-abstraction.md) · [Contents](README.md)

## Sequencing console actions

[`examples/core/console-sequence.fib`](../../examples/core/console-sequence.fib)
contains:

```fibril
main : IO Unit
main = do
  putStrLn "Hello, world!"
  putStrLn "Fibril can sequence console output."
```

`do` sequences action descriptions. Run it with:

```sh
./build/exec/fibril run examples/core/console-sequence.fib
```

The runner validates the plan before executing its supported stdout actions.
This is not a general network, file or effect runtime. For bindings and the
exact supported action forms, see [the console runner](../console-runner.md).

## Make a project

From a directory where you want a new project, invoke the built executable by
its path (or put it on your `PATH`):

```sh
fibril new hello
cd hello
fibril check
fibril run
fibril test
```

This creates a manifest, `src/Main.fib`, and a separate starter test package.
The test is initially a `True` smoke test, not an assertion about console output;
replace it with meaningful pure Boolean checks. Bare commands use the manifest
in the current directory, without searching parent directories. See
[project creation](../project-creation.md) and [libraries and tests](../libraries-and-tests.md).

## Modules

For source-root examples without a manifest, specify both the root and entry:

```sh
./build/exec/fibril check --source-dir examples/modules/records examples/modules/records/Main.fib
```

The entry imports other modules, and checked exported definitions are accessed
using qualified names. Only supported direct imports grant visibility; consult
[modules](../modules.md) for path, export and dependency rules. Local packages
are also supported, with documented restrictions.

## Exercises

1. Create a project and change its greeting. Run `check`, `run`, and `test`.
2. Change the starter test's `True` to `False` and run `fibril test`. Restore it.
3. Follow an import from the records example to its source and locate an export.

## Where next?

Explore the [feature use-case guide](../use-cases.md), the
[language references](../README.md), or the separate
[implementation textbook](../book/00-orientation.md). For the language's
current boundaries, see [checker scope](../erased-checker.md).
