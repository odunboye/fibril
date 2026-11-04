# Bare `Type` as `Type 0`

## Use cases

**Implemented syntax convenience:** write the lowest universe as `Type` when
its level is not the point of the example. For example, an optional value no
longer needs two explicit zeroes in its declaration:

~~~fibril
data Optional (0 A : Type) : Type where
  Nothing : Optional A
  Just : (1 value : A) -> Optional A
~~~

The [runnable example](../examples/modules/bare-type/Main.fib) also uses bare
`Type` in record and interface headers, and retains an explicit `Type 1` for a
higher-universe data declaration:

~~~sh
fibril run --source-dir examples/modules/bare-type examples/modules/bare-type/Main.fib
~~~

Use explicit `Type 0` instead when teaching universe levels, comparing with
higher levels, or making the level visually prominent. This feature adds no
expressiveness or universe-polymorphic inference; it is notation only.

![Bare universe notation](diagrams/bare-type.svg)

## Parsing and checking

- Bare `Type` is parsed as the existing `NSort` level 0 and lowers to the same
  core `Universe 0` as `Type 0`. Its authored source span covers only `Type`.
- `Type 0`, `Type 1` and higher explicit numeric levels keep their existing
  meaning and 1..6 decimal-digit admission. A following numeric token is always
  consumed as the level; an oversized level still reports a parsing error.
- A following nonnumeric atom is not a universe level. For example, `Type x`
  parses as applying `Type 0` to `x`; ordinary resolution/type checking can
  reject that application. It is not an inferred or polymorphic universe.
- The same rule applies to expression atoms and the `Type` result in data,
  record and interface headers. It does not alter level checks, literal-universe
  compatibility, Pi conversion, quantities, termination or cubical foundations.
- `Type` still has type `Type 1`; `Type : Type` is rejected. Bare spelling does
  not mean type-in-type. Existing explicit higher levels remain explicit.

The formatter preserves the authored spelling rather than rewriting `Type 0` to
`Type` or vice versa. Navigation and diagnostics continue to use actual authored
source tokens, not an invented zero. No environment binding or user-overridable
alias named `Type` is introduced.

## Evidence and limits

Tests compare resolved bare/explicit level-zero expressions, check source spans,
malformed numeric levels, ordinary application parsing, data/record/interface
headers, higher-universe checking, formatting/idempotence and a runnable program.
The existing independent core checkers still check the lowered term. These tests
are implementation evidence, not a universe-consistency or whole-language
soundness proof.
