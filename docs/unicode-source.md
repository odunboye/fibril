# Unicode and source text

Status: decoded-text validation implemented; file decoding, identifiers, and
notation remain a design proposal. This is not a surface parser.

## Separate three concerns

1. Source encoding: intended UTF-8 with explicit rejection of malformed bytes.
2. Identifiers: intended Unicode names with specified normalization/security rules.
3. Strings and notation: preserve text data; recognize mathematical aliases only
   as tokens, never through blind global replacement.

An already-decoded Idris String does not prove that its original bytes were valid
UTF-8. A future file loader must validate bytes rather than accept lossy replacement.

## Implemented boundary

[Source.Text](../src/Fibril/Source/Text.idr) validates decoded source and returns
the original String unchanged, or the first rejected scalar's position/reason.

Initial source-wide policy:

- Accept Unicode prose, mathematical symbols, combining marks, emoji, and joiners.
  Acceptance here does not make a character legal in an identifier.
- Allow LF, CRLF, standalone CR, and tabs without rewriting them.
- Reject invalid scalars, other C0 controls, DEL/C1 controls, Unicode line/paragraph
  separators, and BOMs (including an initial BOM).
- Reject raw bidirectional formatting controls: U+061C, U+200E/F, U+202A–E,
  and U+2066–9. This conservative restriction also applies inside comments/strings.

These checks do not detect every invisible or confusable character. Future
identifier checking must address default-ignorables and joiners contextually.
Escaped representation of otherwise forbidden string characters needs a future
literal grammar; it is not implemented.

## Position semantics

Positions use zero-based scalar offsets and one-based logical lines/columns.
An emoji outside the BMP counts as one scalar. Tabs count as one logical column,
not a visual tab stop. CRLF occupies two offsets but advances only one line.
Combining sequences may occupy multiple columns even when displayed as one glyph.

These are not UTF-8 byte offsets, grapheme columns, or LSP UTF-16 positions.
Future editor integration must negotiate/translate position encodings explicitly.

## Proposed identifier policy

- Use a pinned Unicode version and defined identifier tables rather than host
  locale-dependent character predicates.
- Consider UAX #31 identifier profiles with NFC-based canonical lookup, preserving
  original spelling for display and rejecting normalization collisions.
- Define joiner/default-ignorable restrictions and mixed-script/confusable diagnostics.
- Do not normalize whole source files or string data.
- Decide policy for exported names, security-sensitive modules, and ASCII-only
  project profiles explicitly.

No normalization library, identifier tables, collision detector, mixed-script
checker, or Unicode version pin exists yet. These are design gates, not guarantees.

## Proposed mathematical notation

Provide ASCII alternatives for ordinary syntax, such as -> / → and backslash / λ.
Pi/Sigma/equivalence notation needs the corresponding core/surface rules first.
Aliases should elaborate identically and work with formatting, diagnostics, and
Neovim input helpers. No Unicode input method or token aliasing is implemented yet.

## Reading and tests

- [Unicode UAX #31: identifiers and syntax](https://www.unicode.org/reports/tr31/)
- [Unicode UAX #15: normalization](https://www.unicode.org/reports/tr15/)
- [Unicode UTS #39: security mechanisms](https://www.unicode.org/reports/tr39/)

These are design references, not a claim of conformance. Pin specific versions
before implementing identifier behavior.

[Tests.SourceText](../test/src/Tests/SourceText.idr) covers preserved spelling,
non-Latin/combining/astral text, joined emoji, line endings, controls, and positions.
Raw invalid UTF-8 tests wait for the file decoder; source validation is not yet
wired to a file-based CLI command.
