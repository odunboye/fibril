# Design: debugging Fibril programs

Status: **design only, nothing here is implemented.** It states what a debugger can
honestly be today, what is blocked, and the smallest first slice.

## Use case

Answer "why did this term reduce to that?" and "where did my evaluation run out of
fuel?" for a program that already checks. The audience is a Fibril author and a
compiler developer; neither can currently watch a reduction.

## What exists to build on

- `Core.Reduction.step : Term n -> Maybe (Term n)` is a public one-step reducer, and
  `normalize fuel` is built from it. `stepGlobals` also unfolds global references.
- [Fuel laws](reduction-fuel.md) prove `normalizeSplit`: running `a` steps then `b`
  more equals running `a + b`. A stepper that pauses and resumes therefore cannot
  disagree with `eval`. `normalHasNoStep` says when to stop.
- `Core.Pretty.renderTerm` prints core terms, and `check` already prints types.

## What is blocked

- **No source locations.** [Diagnostics](diagnostics.md) states core terms "do not yet
  retain source maps". Any stepper shows *core syntax*, not the lines the author
  wrote. Breakpoints on source lines, a variables panel and DAP integration all need
  core provenance first, which is on the diagnostics roadmap and not started.
- **Effects are not reduced.** `run` prepares an IO plan and the host executes it.
  Stepping pure reduction says nothing about when output happens.
- **Native C backend.** Generated programs have no hooks. Out of scope.
- **Syntax can grow.** The fuel doc notes terms need not shrink. Printing every step
  of a bad program can be enormous, so output must be bounded.

## Slice 1: batch reduction trace (small, no new semantics)

    fibril trace [--steps N] [--width W] PATH

- Runs the same checking as `check` first, so only accepted programs are traced.
- Prints `step 0` (the checked term), then one numbered line per `step`, until the
  term is normal or `N` steps (default 64, at most 4096, matching eval's fuel cap).
- Each term is truncated to `W` characters (default 200) with an explicit `...`
  marker, and the trace stops with a message if the next term would exceed a total
  output budget. Truncation is announced, never silent.
- Ends with `normal form after K steps`, or `stopped after N steps; pending term
  above (continue with a larger --steps)`, reusing `continueNormalization`'s meaning.
- Output goes to stdout. It is a developer aid with **no stability promise**, unlike
  `check --json` ([contract](diagnostics.md#stability-contract-for-check---json)).

Tests (all deterministic, no timing):
1. The last term of a completed trace equals `normalize`'s result for the same fuel.
2. A trace of `a` steps then a trace from its last term for `b` more agrees with a
   trace of `a + b` (the `normalizeSplit` property, checked end to end).
3. An exhausted trace reports how many steps ran and is not mistaken for a normal form.
4. An over-wide term is truncated with the marker, and an ill-typed file is rejected
   before any step is printed.

## Slice 2: interactive stepper (only after slice 1 is used)

`fibril trace --interactive PATH` reading commands from stdin: `step [N]`, `show`,
`unfold GLOBAL` (stepping with that global exposed through `stepGlobals`), `quit`.
Stdin and stdout only, so it works over a pipe and is testable without a terminal.
Breakpoints are limited to **global names**, not source lines (see above).

## Non-goals

DAP or IDE integration, source-line breakpoints, a variable inspector, reverse
stepping, stepping through effect execution, native-code debugging, and debugging
programs that do not check.

## Open questions

1. **Core syntax versus waiting.** Is a core-term stepper useful enough without
   source maps to ship, or should this wait for provenance? Recommendation: ship
   slice 1 labelled "core terms", because it already explains fuel exhaustion.
2. **Names.** Does `renderTerm` keep binder names readable across substitution, or
   does it show indices? This needs checking on real terms before slice 1.
3. **Types.** Should a trace show the type once (as `check` does) or never?
   Recommendation: once, at `step 0`.
