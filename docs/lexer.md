# Minimal expression lexer

Status: implemented tokenization, not parsing or name resolution. The eventual
Idris-like declaration/layout language is not implemented.

## Try it

```sh
./build/exec/fibril lex-source examples/core/identity.fib
```

[The input](../examples/core/identity.fib) uses explicitly annotated expression
syntax now accepted by the [expression parser/checker](parser.md).
Use `fibril check examples/core/identity.fib` for end-to-end ordinary checking.

The CLI strictly loads UTF-8 and validates controls before tokenization, then
prints each token's half-open scalar span, category, and original spelling.
Errors exit nonzero. Token output is diagnostic text, not a machine protocol.

## Tokens

| Kind | Accepted spelling |
| --- | --- |
| Identifier | ASCII letter or underscore, followed by ASCII letters/digits/underscore/apostrophe |
| Natural digit sequence | One or more ASCII digits; spelling retained without integer conversion |
| Keywords | Exactly Type, let, in; Type0, letter, inner remain identifiers |
| Grouping/annotation/binding | ( ) : = |
| Lambda | Backslash or λ |
| Function arrow | -> or → |
| Body arrow | => or ⇒ |

Unicode notation aliases share a token category but retain original spelling.
No global rewriting occurs. Unsupported characters fail explicitly.

Whitespace (space/tab/LF/CR/CRLF) and -- line comments are skipped. Comments may
contain ordinary Unicode text, but source-wide forbidden controls are still
rejected. There are no strings, operators beyond this table, block comments,
indentation tokens, or general Unicode identifiers yet.

## Spans and progress

Tokens carry original spelling and exclusive-end SourceSpan positions. The lexer
and validator share advancePosition. CRLF is processed as a complete pair;
splitting it across calls would incorrectly advance two lines.

An internal progress budget starts at the decoded scalar count and decreases per
scan iteration. Every iteration consumes at least one scalar, including skipped
comments/whitespace. The budget guarantees recursion structure, not wall time,
stack usage, or memory safety against arbitrarily large in-memory inputs.
The file loader's independent byte limit remains in effect for CLI inputs.

## Responsibilities

- [Source.File](../src/Fibril/Source/File.idr): bounded byte loading/UTF-8 decoding.
- [Source.Text](../src/Fibril/Source/Text.idr): source control policy and positions.
- [Source.Lexer](../src/Fibril/Source/Lexer.idr): expression tokens and spans.
- Source.Parser: implemented expression structure and bounded numeric interpretation.
- Source.Resolve: implemented lexical scopes/names to bounded core indices.
- Existing checkers: typing and resource policy, not tokenization.

ASCII identifiers are a deliberately narrow starting point. A versioned Unicode
identifier profile and normalization/confusable policy must precede extending
them; mathematical aliases do not bypass that requirement.

## Tests and next step

[Tests.Lexer](../test/src/Tests/Lexer.idr) checks aliases, keyword boundaries,
original spelling, CRLF/tab/astral-comment spans, unsupported punctuation,
and validation before comment skipping. CLI smoke tests load actual files.

The [expression parser](parser.md) now consumes these tokens into named syntax;
resolution remains a separate pass. Declaration/layout syntax and package-manifest
parsing remain future work; the YAML manifest must not reuse this lexer.
