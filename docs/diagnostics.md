# Source and type diagnostics

Status: implemented plain-text point diagnostics, not an LSP protocol or a
source map for core typing.

## What file commands report

check, check --erased, eval, and lex-source retain located lexer/parser/name
resolution failures and render them against the original loaded text:

    broken.fib:1:1: Resolution: Unbound name "missing"
      1 | missing
        | ^

These commands still exit nonzero on failure and use their existing stdout
reporting. The separate run command reserves stdout for program output and
reports failures on stderr.
IO/UTF-8/text-loading failures include the filename but have no source excerpt:
the loader did not return validated text.

Core typing, usage, normalization, and post-reduction failures also include the
filename but **no invented caret**. Core terms do not yet retain source maps.

## Coordinates and presentation limits

[Source.Diagnostic](../src/Fibril/Source/Diagnostic.idr) uses the existing
[scalar positions](unicode-source.md), not bytes, UTF-16, grapheme clusters, or
terminal-cell coordinates.

- CRLF is one line break; bare CR and LF also break lines.
- Tabs display as one space, matching the logical-column policy.
- Empty input and EOF on/after a newline can have a caret.
- An excerpt contains at most 80 original scalars, centered with up to 40 before
  the point; omitted sides display ASCII ellipses.
- Filename and message labels each retain at most 256 original scalars.
- Controls and rejected formatting scalars display as decimal <codepoint>
  markers rather than terminal instructions. Their escape widths affect padding.
- Valid Unicode spelling is preserved, but combining/wide glyphs may make a
  caret differ from physical terminal-cell alignment.

These are output bounds, not bounds on traversal work, allocation, or process
resources. Callers must provide positions from the same unchanged source text.
The renderer does not verify offset/line/column consistency; defensive column
clamping prevents enormous padding, not invalid provenance.

## Types in core rejection reports

An explicit mismatch now includes the inferred and expected core types:

    bad.fib: Runtime checking: Inferred type is not compatible with expected type; inferred: Bool; expected: Unit

This is the error for (True : Unit). A conditional with True versus () branches
reports then: Bool; else: Unit. Applying () reports a nonfunction type, found: Unit.

[CheckError](../src/Fibril/Core/Erased.idr) now retains:

- TypeMismatch: the original inferred and expected terms in one shared scope.
- BranchTypeMismatch: both originally inferred branch types in one shared scope.
- ExpectedFunction/ExpectedUniverse: the type after weak-head exposure that failed
  the required shape test.
- CheckingLimit/ReductionLimit: distinct exhaustion errors, never fabricated
  mismatch witnesses.

The existential scope index is erased; this preserves the relation between the
stored terms without requiring a runtime scope size. Payloads are ordinary scoped
syntax, not evidence of typing or inequality. They may include newest-first
indices such as v1 and do not recover source names.

Rendering uses [Pretty.renderTerm](../src/Fibril/Core/Pretty.idr). It does not
normalize again, spend reduction fuel, or infer source spans. A mismatch payload
can therefore still contain redexes. File-level output retains the label length
bound; the structured error preserves its complete payload even if text is
truncated. Constructing/rendering a large payload is not a bounded-work promise.

## Structured driver boundary

[Driver.Check](../src/Fibril/Driver/Check.idr) exposes DriverError:

- FrontendFailure retains LexError, ParseError, or ResolveError.
- ErasedFailure retains CheckError; RuntimeFailure retains RuntimeError.
- EvaluationLimit distinguishes evaluation exhaustion.
- ConsoleFailure retains structured argument resolution, typing, reduction, and
  post-check errors. Name errors keep resolver carets; core failures identify the
  argument root in their message without pretending to locate the failing subterm.
- EffectfulEvaluation and ErasedConsole reject console actions at the ordinary
  normalization/erased-proof boundaries; malformed strings retain lexical points.
- PostReductionFailure retains the runtime error from final rechecking.

RuntimeError's TypingError in turn retains the structured CheckError. No core
payload is flattened to a string until a presentation API is requested.

checkSourceDetailed, prepareRuntimeSourceDetailed, and
[evaluateSourceDetailed](../src/Fibril/Driver/Evaluate.idr) preserve these
errors until presentation. File commands parse/check once and choose contextual
rendering afterwards, rather than rerunning the frontend to recover a location.

The existing checkSource, prepareRuntimeSource, and evaluateSource APIs still
return the same plain-string result types, with richer mismatch messages. Future IDE integration can
consume structured failures, but must implement an explicit UTF-16 mapping and
cannot treat current core messages as exact source ranges.

## Tests and next work

[Tests.Diagnostic](../test/src/Tests/Diagnostic.idr) covers line endings, tabs,
EOF, long lines/labels, clamped padding, Unicode spelling, control escaping,
structured errors, and unlocated core failures.
[Tests.CheckDiagnostic](../test/src/Tests/CheckDiagnostic.idr) adds closed/open
payloads, shape and branch errors, no-normalization rendering, and preservation
through each driver stage. CLI tests use actual files for
check/eval/lex diagnostics and retain nonzero exits.

Next steps include core provenance through elaboration, exact ranged spans,
multiline diagnostics, related locations, suggestions, and machine protocol
encoding. Terminal rendering is a presentation layer, not additional checking
evidence or a change to the trusted core.
