# Source formatting

**Implemented:** deterministic horizontal token-spacing normalization.
Indentation, wrapping, automatic editor formatting, --write, and whole-project
rewriting are not implemented. This formatter never writes the input file.

~~~sh
./build/exec/fibril format examples/core/hello-world.fib
./build/exec/fibril format --check examples/core/hello-world.fib
~~~

format PATH emits formatted source to stdout. format --check PATH emits nothing
on success and returns nonzero with a stderr message when formatting is required.
Malformed/invalid UTF-8 or source-policy failures also return nonzero. Formatting
failure emits no partial source. Unexpected process termination is outside these
represented-error guarantees.

Never redirect output onto the input path: the shell may truncate it before
Fibril opens it. Inspect stdout or use a separate temporary destination. No
automatic save, formatter-on-save, import lookup, program execution, or package
configuration is involved.

## Current style

Same-line horizontal gaps between tokens become one ASCII space, except:

- No spaces next to qualified-name dots.
- No space immediately inside parentheses, including ().
- No space between lambda and its opening binder parenthesis.

For example:

~~~text
main:IO  Unit
main=putStrLn(appendString"Hello"", Fibril!")
~~~

becomes:

~~~fibril
main : IO Unit
main = putStrLn (appendString "Hello" ", Fibril!")
~~~

The formatter preserves original token spelling, including string escapes,
Unicode and arrow/lambda glyphs. It changes gaps, not literal values or identifiers.

It preserves every gap that is not exclusively same-line spaces/tabs. In
particular, indentation, blank lines, line comments, comment spacing, trailing
gaps, LF/CRLF and final-newline presence are retained. Same-line tabs **between**
tokens become canonical spaces; leading tabs do not. Lines are not joined or
split, avoiding changes to the existing do/record layout restrictions.

This deliberately leaves alignment, trailing whitespace, indentation and long
lines unchanged. It is a conservative first formatter, not a complete style
engine or a canonical representation of all source trivia.

## Structural safety boundary

[Source.Format](../src/Fibril/Source/Format.idr) parses the original bounded source,
rewrites token gaps using scalar spans and original character slices, then parses
the complete candidate again. [Source.Shape](../src/Fibril/Source/Shape.idr)
compares the parsed structures, ignoring source positions but preserving:

- Module/import identities and document structure.
- Ordinary declaration names, quantities, signatures, values and export flags.
- Record parameters, ordered field types/quantities, constructor/eliminator names,
  projection requests and export policy.
- Expression constructors, binders, names, literals, quantities, branches and
  explicit motives.

Candidate parsing/shape differences reject formatting rather than emitting a
guessed result. Both input and output must fit 65,536 UTF-8 bytes; spacing
insertion cannot evade the output bound.

This is a runtime guard and test evidence, not a theorem of semantic equivalence,
typing preservation, quantitative soundness or complete comment preservation for
future syntax. New syntax must extend the shape comparison before formatting
accepts it. The source is not elaborated or typechecked: invalid method bodies or
unsafe projection requests can still be syntactically formatted.

The [named-IR inspection printer](elaboration.md) is separate. Its generated
expressions/internal names are not source formatting input or a round-trip format.

## Evidence and next steps

Tests check exact comments/literals and line endings, empty/comment-only/no-final-
newline inputs, indentation retention, invalid byte/BOM/control/syntax failures,
output-size admission, idempotence and unchanged original files. Current core
example fixtures are formatted twice and rechecked for the same acceptance status.

Next steps are lossless trivia-aware indentation/wrapping, broader source corpus
tests, and an explicit editor buffer operation. Do not attach the current stdout
command to format-on-save through an untested adapter or treat it as an in-place
formatter.
