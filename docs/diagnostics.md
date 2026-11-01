# Located frontend diagnostics

Status: implemented plain-text point diagnostics, not an LSP protocol or a
source map for core typing.

## What file commands report

check, check --erased, eval, and lex-source retain located lexer/parser/name
resolution failures and render them against the original loaded text:

    broken.fib:1:1: Resolution: Unbound name "missing"
      1 | missing
        | ^

Failures still exit nonzero and use the CLI's existing stdout reporting.
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

## Structured driver boundary

[Driver.Check](../src/Fibril/Driver/Check.idr) exposes DriverError:

- FrontendFailure retains LexError, ParseError, or ResolveError.
- DriverFailure retains unlocated checker/evaluator messages.

checkSourceDetailed, prepareRuntimeSourceDetailed, and
[evaluateSourceDetailed](../src/Fibril/Driver/Evaluate.idr) preserve these
errors until presentation. File commands parse/check once and choose contextual
rendering afterwards, rather than rerunning the frontend to recover a location.

The existing checkSource, prepareRuntimeSource, and evaluateSource APIs still
return their original plain-string presentations. Future IDE integration can
consume structured failures, but must implement an explicit UTF-16 mapping and
cannot treat current core messages as exact source ranges.

## Tests and next work

[Tests.Diagnostic](../test/src/Tests/Diagnostic.idr) covers line endings, tabs,
EOF, long lines/labels, clamped padding, Unicode spelling, control escaping,
structured errors, and unlocated core failures. CLI tests use actual files for
check/eval/lex diagnostics and retain nonzero exits.

Next steps include core provenance through elaboration, exact ranged spans,
multiline diagnostics, related locations, suggestions, and machine protocol
encoding. Terminal rendering is a presentation layer, not additional checking
evidence or a change to the trusted core.
