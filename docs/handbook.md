# Browsable handbook

## Build and browse

Prerequisites: the normal pack/Idris bootstrap toolchain, Python 3, Pandoc, and
Graphviz (`dot`). No Python packages, JavaScript framework, or CDN is required.

From the project root:

```sh
make handbook
make serve-docs
```

Open http://127.0.0.1:8000. Alternatively open `build/handbook/index.html`
directly for offline browsing. The server binds only to localhost.

## Refreshing rebuilt pages

`make serve-docs` serves on loopback with `Cache-Control: no-cache`, so browsers
revalidate HTML and assets. CSS and UI-script URLs also contain content hashes,
which change when those files change. This prevents old styles from masking a
new build; it does not require clearing the browser's entire cache.

If an older server/session is still open, rebuild, restart the server, and reload
once with Cmd+Shift+R (macOS) or Ctrl+Shift+R. An added URL query such as
`?refresh=1` also requests a fresh page. Browser reader/dark-mode/custom-style
extensions can still alter colors; disable those for localhost when diagnosing.
Current highlighting uses different keyword/type/comment colors in both themes.

To serve an existing build on another port without rebuilding, use
`python3 tools/serve_handbook.py --port 8001`. The helper is a local development
server, not a production hosting/security boundary.

## Textbook organization

The landing page, **Building Fibril**, introduces eight ordered implementation
chapters: orientation, binding, quantities, contexts/reduction, checking, cubical
infrastructure, testing/maintenance, and the roadmap. Each includes learning
goals, explanations, source-reading exercises, and references. Previous/next
links follow this sequence.

Part II holds technical references; Part III preserves project records.
`docs/book.json` owns part labels, titles, and order. New pages must be listed;
the generator rejects missing, duplicate, or unlisted pages. Markdown owns content.

Navigation regression tests verify current-page markers, chapter ordering, and
landing-page links. Browser rendering and fragment targets remain manual checks.

## Reading experience

The offline theme adapts [Kanso](https://github.com/webhooked/kanso.nvim):
Pearl's soft neutral paper in light mode and Ink's charcoal backgrounds with
muted gray-green text in dark mode. Blue-gray accents remain restrained.
Palette reference: [upstream colors](https://github.com/webhooked/kanso.nvim/blob/main/lua/kanso/colors.lua).
The Pearl link color is slightly darkened to retain contrast on secondary surfaces. A 66-character reading measure, 20px default
Atkinson Hyperlegible prose, generous line height, and balanced chapter headings support extended
reading. Compact sans-serif navigation stays visually separate from the text.
Diagrams adapt to dark mode. This is an original adaptation, not the official
Kanso theme or a claim that any palette prevents eye strain.

Automated palette checks require body-text contrast of at least 7:1 and muted/
link text of at least 4.5:1 on reading, panel, and code surfaces. These checks do
not replace a complete accessibility or visual review.
A grouped sidebar separates the teaching path from references and records.

With JavaScript enabled:

- Search local documentation text with the search box or the / shortcut.
- Use the page outline to jump between sections.
- Change reading size and light/dark theme; preferences are stored locally
  when browser storage is available. Otherwise the controls still work per page.
- Copy code blocks (clipboard permission/security restrictions may require
  manual selection instead).
- Use the mobile Menu control; Escape closes it.
- See estimated reading time and scroll progress.

Without JavaScript, chapter content, navigation, source links, and system-theme
styling remain available. Print styling removes navigation and controls.
Reduced-motion preferences disable animated scrolling/transitions.

Typography uses bundled Atkinson Hyperlegible Next for prose, headings,
navigation, and tables; Atkinson Hyperlegible Mono for code. Both include normal
and italic variable fonts (weights 200–800) with font-display: swap. They load
locally without a third-party font service; system fonts remain fallbacks for
loading failures or missing glyphs.

Fonts are redistributed unmodified under SIL Open Font License 1.1. Upstream
copyright/license notices are included in docs/assets/fonts/OFL-Next.txt and
OFL-Mono.txt; manifest.json records pinned upstream revisions and SHA-256 hashes.
The font designers and Braille Institute are credited in upstream notices; use
here does not imply endorsement. See
[Atkinson Hyperlegible Next](https://github.com/googlefonts/atkinson-hyperlegible-next)
and [Mono](https://github.com/googlefonts/atkinson-hyperlegible-next-mono).
 Code disables
ligatures and uses lining numerals; tables and source lines use tabular numerals.
Paragraphs and lists use consistent relative spacing, headings request balanced
wrapping, and print rules avoid stranded headings. Browser support for advanced
wrapping varies; ordinary wrapping remains the fallback.

Saved text-size preferences are preserved; use A+ if an earlier 18px setting is
still active. New readers start at 20px, with controls allowing 15–23px.

Theme assets live in docs/assets/book.css and book.js. The builder generates
a local search-data.js, so search needs neither a server API nor a CDN.
Search covers documentation text, not the full source tree or generated API.
API pages retain the Idris documentation generator's own presentation.

Automated checks cover local asset presence, font hashes/licenses and CSS
references, search-index chapter inclusion, and navigation. JavaScript syntax is checked with Node during development;
actual browser rendering, interaction, and accessibility are not yet covered
by automated browser tests.

## Code highlighting

Both fenced examples and the linked source browser now have offline syntax colors:

- Use `fib` or `fibril` fences for Fibril. A local Skylighting grammar recognizes
  current keywords, quantities, Unicode operators, comments, strings, and escapes.
- Use `idr` or `idris` fences for Idris. Pandoc supplies its built-in Idris grammar.
- `.fib` and `.idr` source pages select the appropriate grammar automatically.
  Other source formats retain their escaped plain-text rendering.

For example:

```fib
main : IO Unit
main = putStrLn "Hello, world!"
```

```idris
executeConsole (PrintLine text) = do
  result <- fPutStrLn stdout text
  pure $ case result of
    Left err => Left ("Console output failed: " ++ show err)
    Right () => Right ()
```

The handbook's Pearl/Ink palettes style the generated token spans, including
system/explicit dark mode. Token colors are tested for at least 4.5:1 contrast on
the code surface. Fonts, copying, source line numbers, and existing #L-number
links are retained. Highlighting happens during the build: no browser highlighter,
CDN, or extra package is needed.

This is lexical presentation, not compiler checking or semantic symbol coloring.
The local Fibril grammar and editor runtime are separate presentation definitions;
compiler diagnostics remain authoritative. An IO-looking name being colored does
not make it available in the ordinary core. The Idris appearance depends on the
installed Pandoc grammar, not a Fibril checker.

Source rendering protects fence delimiters and HTML data, restores Pandoc-trimmed
trailing blank lines, and fails if expected line anchors cannot be preserved.
Handbook tests cover both languages, logical source text/anchors (including tabs), escapes/comments,
HTML/fence handling, and theme contrast.

## Included material

- A responsive sidebar across the documentation pages.
- The complete design record and current specifications/proposals.
- An implementation tour with module dependency and selected call diagrams.
- A roadmap diagram visibly separating planned stages from implementation.
- Source pages with line anchors for core, tests, and runnable examples.
- Idris-generated API documentation.
- Contributor guidance, proof examples, and dependency evaluation findings.

The static generator is `tools/build_handbook.py`. It converts tracked Markdown
through Pandoc, renders DOT diagrams through Graphviz, and links generated source
pages. It deletes and rebuilds only `build/handbook`. Generated output is ignored.

## Maintaining accuracy

- Edit Markdown and DOT sources, not generated HTML or SVG.
- Update the curated graph when adding or changing relevant calls.
- Call arrows show selected direct calls, not runtime sequencing or proof evidence.
- Module arrows show direct project imports, not transitive imports.
- Run `make handbook` after documentation changes.
- The build checks local HTML file links outside generated API internals.
  It does not yet validate fragments, external URLs, accessibility, or browser
  rendering automatically.
- The API generator's internal links are its responsibility; generation must
  succeed, but full API link integrity is not asserted.

Current tooling is a lightweight offline handbook rather than a full GitBook
service. Search, release hosting, and automatic call-graph extraction can be
added when needed without changing the Markdown source of truth.
