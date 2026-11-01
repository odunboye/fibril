# 1. What are we building?

## Learning goals

Understand Fibril's intended language, distinguish implemented infrastructure
from aspirations, and run the project before reading its internals.

Fibril aims to combine Idris-like dependent programming and quantities with
computational HoTT. Idris 2 is the host language: it compiles our implementation.
It is not the same language as the future Fibril surface syntax.

Today you can check a small annotated expression source file, construct core
terms as Idris values, and run tests. You cannot compile Fibril source to C or JS.
Try `fibril check examples/core/identity.fib`; see the [grammar](../parser.md).
You can now also run `fibril run examples/core/hello-world.fib` through a
[hosted IO-description runner](../console-runner.md), using checked Fibril
prelude functions. Reference normalization never performs writes; a complete
IO calculus and backend remain future work.

## The three layers to keep separate

1. **Theory:** the mathematical judgments we intend to implement.
2. **Representation:** Idris data structures encoding syntax and contexts.
3. **Algorithms:** substitution, reduction, inference, and usage checking.

A well-scoped representation does not establish typing. A passing type checker
does not prove its own correctness. A citation does not fill either gap.

![Implemented dependencies](../diagrams/modules.svg)

Arrows point from importer to dependency. This is the current module structure;
it is not the order in which every algorithm executes.

## Run the implementation

From the repository root:

```sh
pack build fibril
./build/exec/fibril demo
pack test fibril
pack run fibril-examples
make handbook
```

Pack pins the bootstrap collection. Tests run deterministic regressions and
Hedgehog properties. Examples include actual Idris proofs and calls to Fibril's
prototype checkers; the distinction matters.

The [demo command](../cli.md) prints a checked polymorphic identity, shows runtime
usage validation, rejects linear duplication, and checks cubical algebra laws.
The displayed terms are explicit diagnostic syntax, not parsed source files.

## Source text is a separate boundary

[Unicode source validation](../unicode-source.md) now preserves decoded text and
rejects selected controls with scalar positions. Strict UTF-8 decoding and bounded
file loading are now available through `fibril validate-source PATH`. Unicode
identifier rules and normalization are not implemented. A [minimal lexer](../lexer.md)
now recognizes ASCII names and explicit lambda/arrow aliases, but not layout or
full-language syntax. Run `fibril lex-source examples/core/identity.fib` to inspect it. This
boundary sits before future lexing and does not alter the nameless core.

## A first reading route

Read Quantity and Term, then Context and Reduction, then Erased and Runtime.
Read Interval, Face, Scope, and Restriction as a parallel branch: these currently
provide cubical infrastructure, not cubical term checking.

## Check your understanding

- Why can a Fin-bounded variable still occur in an ill-typed term?
- Why does compiling the implementation successfully not prove logical soundness?
- Which current example invokes a Fibril checker rather than only Idris?

**Reading:** [implementation tour](../implementation-tour.md),
[architecture](../architecture.md), [examples](../../examples/README.md).

**Status:** orientation to working prototypes; no full-language guarantees.
