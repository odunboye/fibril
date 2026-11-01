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

The offline theme is strictly monochrome: white paper and black ink in light
mode, near-black paper and light ink in dark mode. Neutral grays, spacious type,
comfortable reading width, subtle borders, and serif chapter headings provide
hierarchy without colored accents. Diagrams adapt to the dark background.
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

Theme assets live in docs/assets/book.css and book.js. The builder generates
a local search-data.js, so search needs neither a server API nor a CDN.
Search covers documentation text, not the full source tree or generated API.
API pages retain the Idris documentation generator's own presentation.

Automated checks cover local asset presence, search-index chapter inclusion,
and navigation. JavaScript syntax is checked with Node during development;
actual browser rendering, interaction, and accessibility are not yet covered
by automated browser tests.

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
