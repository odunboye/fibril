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
- ConsoleFailure retains IO-planning errors. Source names, including prelude
  functions, use the ordinary resolver and retain real source points. Core/planner
  failures remain unlocated rather than acquiring guessed subterm carets.
- PreludeUnavailable reports bundled library errors without assigning embedded
  library positions to the user's source file.
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

## Structured runtime-check reports

~~~sh
./build/exec/fibril check --json examples/core/string-equal.fib
~~~

This emits one version-1 JSON object on stdout, including on represented checking
or file-loading failures. Exit status is 0 for acceptance and nonzero for rejection.
Normal represented failures leave stderr empty; a client must decode the report
rather than assuming every nonzero exit means malformed JSON. Unexpected process
termination or host failures are not guaranteed to produce a report.

The fields are:

- coordinates: unicode-scalars;offset=0;line=1;column=1, matching navigation.
- accepted: the experimental runtime checker's decision, not a soundness proof.
- report: informational lines on success; empty on rejection.
- diagnostics: empty on success, otherwise the first failure. Recovery and
  multiple-error accumulation are not implemented.

Each diagnostic has severity ("error"), stage, message, position, and byteOffset.
position is either a real scalar point or null. Core type/resource errors and
file-level failures remain **unlocated**, with no invented line-one range.
Decoding errors instead provide a zero-based byteOffset and null scalar position;
these offsets must not be treated as UTF-16/scalar editor columns. Source-policy
failures after decoding can retain their real scalar point.

Stages currently distinguish loading, decoding, source-validation, lexing,
parsing, resolution, prelude, and runtime-checking. The report representation can
also render existing erased/evaluation/post-reduction/IO-planning driver errors;
the new command itself runs ordinary runtime checking only, not those services.

[Driver.CheckReport](../src/Fibril/Driver/CheckReport.idr) exposes checkReport for
unsaved source Strings, checkFileReport for bounded files, and structured outcome
constructors retaining DriverError/LoadError. The public data constructors are
not checking certificates. JSON string escaping and protocol metadata are shared
with the navigation commands through [Driver.JSON](../src/Fibril/Driver/JSON.idr).

The old human-readable check and check --erased interfaces are unchanged.
check --json never executes IO descriptions, writes source, or invokes a backend.
It is not an LSP, UTF-16 adapter, or incremental checker. The optional
[FibrilCheck editor adapter](editor-highlighting.md#runtime-checking-in-the-editor)
uses this report without inventing locations for unlocated errors.

## Source-aware project reports (version 2)

~~~sh
./build/exec/fibril check --json --source-dir examples/modules/checked examples/modules/checked/Main.fib
~~~

This reports project acceptance/rejection without executing IO descriptions.
Represented rejections still emit JSON on stdout with nonzero status and empty
stderr. Unexpected process termination is outside this guarantee.

Version 2 deliberately is **not** the single-file version-1 schema. In addition
to the scalar coordinates, accepted, report, and diagnostics fields, it contains:

- entry: canonical entry path after discovery, otherwise its requested spelling.
- root: canonical root after complete discovery, otherwise null.
- sources: path/text objects containing exact immutable source snapshots. A known
  empty file has text ""; an unavailable source is not fabricated as an empty file.
- Each diagnostic includes path, stage, message, severity, position, byteOffset,
  and sourceAvailable. Scalar points and byte-only decoding offsets stay distinct.

Paths are canonical for discovered files; an early filesystem failure can retain
the request path without claiming canonical identity. Unlocated core errors
remain null positions, even when their source text is available. A scalar-policy
failure can have a real point but unavailable text because the bounded loader
rejected the decoded source. No blank excerpt is invented for it.

[ProjectOutcome](../src/Fibril/Driver/ModuleCheck.idr) now retains the loaded graph
when checking fails; plain project check/eval/run and
[Driver.ProjectReport](../src/Fibril/Driver/ProjectReport.idr) share that preparation.
Graph-discovery failure may retain only the error site's source, not a complete
graph. Reports currently contain the first error, not recovery/multiple failures.

**Reports include project source code**, including private definitions. Do not
treat this as a redacted log format. Successful/fully loaded checking reports can
carry all reachable source texts within the graph limits. Byte counts and source
snapshots do not establish authenticity or an atomic filesystem transaction.

Clients must verify file identity and snapshot contents against the relevant
buffers/files before attaching diagnostics or trusting a displayed acceptance.
A dependency point must never be converted against the entry buffer. The version-1 FibrilCheck adapter intentionally rejects version 2. The separate
[FibrilCheckProject adapter](editor-highlighting.md#project-checking-in-the-editor)
validates source identities/snapshots and only maps points into already-loaded
UTF-8 buffers. Existing single-file JSON remains version 1.

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
