# 1. Getting started

[Contents](README.md) · [Next: Values and functions](02-functions.md)

## Build Fibril

Install the Idris 2 `pack` tool and the bootstrap prerequisites described in the
[project README](../../README.md#build), then from the repository root run:

```sh
pack build fibril
./build/exec/fibril --help
```

The following file, [`examples/core/hello-world.fib`](../../examples/core/hello-world.fib),
describes a console program:

```fibril
main : IO Unit
main = putStrLn "Hello, world!"
```

Run it with:

```sh
./build/exec/fibril run examples/core/hello-world.fib
```

`main` has the type `IO Unit`: it describes an action whose result carries no
interesting information. `putStrLn` describes printing a line. The hosted runner
checks and executes supported console plans; it is not general-purpose IO.

## Three ways to inspect a program

```sh
./build/exec/fibril check examples/core/declarations.fib
./build/exec/fibril eval examples/core/declarations.fib
./build/exec/fibril run examples/core/console-sequence.fib
```

`check` validates a program without running it. `eval` checks and reduces a
pure entry point; here its normal form is `True`. `run` executes a supported
console plan. Evaluation is bounded reference reduction, not compiled execution.
See the [CLI reference](../cli.md) for options.

## Exercises

1. Copy the hello-world example to a new `.fib` file, change its message, and run it.
2. Check and evaluate `examples/core/boolean.fib`. What does its entry point return?
3. Change the first line's type in your copy to `Bool` and observe the diagnostic.
