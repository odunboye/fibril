# Source formatting

**Implemented:** deterministic horizontal spacing and guarded wrapping of long
applications, lambdas, signatures and case/conditional expressions. Manual :FibrilFormat buffer application is available
in Vim/Neovim. General indentation/reflow, format-on-save, --write, and whole-project
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

## Editor usage

Use [:FibrilFormat](editor-highlighting.md#formatting-in-vim-and-lazyvim) to format
the current buffer, including unsaved edits. It applies one undoable change and
never saves the source. The LazyVim setup includes an optional <leader>cf mapping;
there is no default key or format-on-save hook.

format --json PATH returns version-1 original/formatted snapshot fields for the
adapter. It is still syntax-only and uses the same guarded formatter. The editor
formats a private temporary snapshot, not stale on-disk source.

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

It preserves comments, literal spelling, blank lines, trailing gaps, LF/CRLF and
final-newline presence. Gaps containing comments are never replaced. At planned
syntax boundaries a whitespace-only gap can gain a newline or continuation
indentation; it is not a general block-indentation pass. Same-line tabs **between**
tokens become canonical spaces. Existing indentation is retained except at
syntax-selected continuation breaks. Existing lines are not joined. Only the guarded application-wrapping rule below
inserts line breaks, avoiding unsupported do/record layout changes.

This deliberately leaves alignment, trailing whitespace and existing indentation
outside selected syntax boundaries. Long structured expressions receive
continuation indentation. It is a conservative first formatter, not a complete style
engine or a canonical representation of all source trivia.

## Structured expression layout

The soft target is 100 Unicode-scalar columns, with conservative prefix allowance.
Layout uses flattened token widths rather than current physical line widths, so
already-multiline values are not skipped and repeated formatting is stable.
Grouped/long application arguments, lambda bodies, Pi signature chains, case
return/of/body boundaries and conditional branches receive syntax-directed
continuation breaks, normally in two-space steps. For example:

~~~fibril
main = putStrLn
  (Data.Message.render
    (Data.Message.MkMessage True
      (Data.Package.recover
        (Data.Package.MkPackage String "Records"))))
~~~

Breakpoints come from expression spans and actual arrow/keyword tokens, not
splitting arbitrary tokens or strings. Synthetic pattern lambdas are distinguished
from authored arrows, so the two pattern binders stay together. Qualified names and literal spelling are preserved. Existing line
breaks/blank lines are retained; final-newline presence is unchanged. Homogeneous
LF or CRLF style is used for inserted breaks. Mixed/lone-CR input receives
spacing-only formatting.

The proposed layout is reparsed and structurally compared. If it cannot preserve
the parsed document, formatting falls back to spacing only. Oversized wrapping
also falls back. This is not a universal line-length guarantee: long literals,
long indivisible names, record headers/single-line field declarations and
expressions containing physical-line do statements are not generally reflowed.
Comments can prevent a desired breakpoint. Source wrapping is still conservative,
not a complete width-constrained pretty printer. Reformatting emitted layout is idempotent.

The Vim/Neovim adapter accepts inserted lines as one undoable buffer change.
It checks unchanged non-whitespace content, blank lines, final-newline/style
options and snapshot identity; the compiler remains responsible for literal and
AST-shape validation. It does not run a second language parser in the editor.

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

Next steps are broader trivia-aware indentation/reflow and source corpus
tests, and optional editor format-on-save integration after validation. Do not attach the current stdout
command to format-on-save through an untested adapter or treat it as an in-place
formatter.
