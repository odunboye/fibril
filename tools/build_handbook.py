#!/usr/bin/env python3
"""Build an offline handbook using pandoc/Graphviz, with linked source pages.

Only local project files are read; no CDN assets or network access are required.
Call graphs are curated DOT files, not inferred correctness evidence.
"""
from pathlib import Path
import html
import json
import os
import re
import shutil
import subprocess
from html.parser import HTMLParser

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build/handbook"


def relative(target, page):
    return os.path.relpath(target, page.parent).replace(os.sep, "/")


def main():
    for tool in ("pandoc", "dot"):
        if not shutil.which(tool):
            raise SystemExit(f"Missing prerequisite: {tool}")
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    pages = sorted((ROOT / "docs").rglob("*.md")) + [
        ROOT / "README.md", ROOT / "CONTRIBUTING.md",
        *sorted((ROOT / "examples").rglob("*.md")),
    ]
    sources = sorted((ROOT / "src").rglob("*.idr")) + sorted(
        (ROOT / "test/src").rglob("*.idr")) + sorted(
        (ROOT / "examples/src").rglob("*.idr"))
    destinations = {p: OUT / p.relative_to(ROOT).with_suffix(".html") for p in pages}
    destinations.update({p: OUT / "source" / (str(p.relative_to(ROOT)) + ".html")
                         for p in sources})
    # One manifest owns reading order and labels; Markdown owns chapter content.
    parts = json.loads((ROOT / "docs/book.json").read_text())
    nav = [("Book contents", OUT / "index.html")]
    titles = {}
    for part in parts:
        nav.append((part["title"], None))
        for entry in part["pages"]:
            source = (ROOT / entry["path"]).resolve()
            if source not in destinations or source in titles:
                raise SystemExit(f"Missing or duplicate book page: {entry['path']}")
            titles[source] = entry["title"]
            nav.append((entry["title"], destinations[source]))
    unlisted = [p for p in pages if p not in titles]
    if unlisted:
        raise SystemExit("Add pages to docs/book.json: " + ", ".join(str(p.relative_to(ROOT)) for p in unlisted))
    nav += [("Source and API", None), ("Source index", OUT / "sources.html"),
            ("API reference", OUT / "api/index.html")]
    chapters = [destinations[(ROOT / e["path"]).resolve()]
                for e in parts[0]["pages"]]
    shutil.copytree(ROOT / "docs/assets", OUT / "assets")
    search_index = []

    def write_page(path, title, body):
        path.parent.mkdir(parents=True, exist_ok=True)
        links = ""
        for label, dest in nav:
            if dest is None:
                links += f'<h3>{html.escape(label)}</h3>'
            else:
                current = ' aria-current="page"' if dest == path else ''
                links += f'<a{current} href="{html.escape(relative(dest, path))}">{html.escape(label)}</a>'
        if path in chapters:
            position = chapters.index(path)
            previous = chapters[position - 1] if position else OUT / "index.html"
            following = chapters[position + 1] if position + 1 < len(chapters) else OUT / "docs/references.html"
            body += (f'<footer aria-label="Chapter navigation"><a href="{relative(previous, path)}">← Previous</a>'
                     f'<span>Chapter {position + 1} of {len(chapters)}</span>'
                     f'<a href="{relative(following, path)}">Next →</a></footer>')
        prefix = relative(OUT, path) + "/"
        page_class = "contents" if path == OUT / "index.html" else "source-page" if OUT / "source" in path.parents else "chapter"
        badge = "The implementation textbook" if path in chapters or page_class == "contents" else "Fibril · Technical reference"
        path.write_text(f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
                        f'<meta name="viewport" content="width=device-width,initial-scale=1">'
                        f'<meta name="color-scheme" content="light dark">'
                        f'<title>{html.escape(title)} — Fibril</title>'
                        f'<link rel="stylesheet" href="{prefix}assets/book.css">'
                        f'<script defer src="{prefix}assets/search-data.js"></script>'
                        f'<script defer src="{prefix}assets/book.js"></script></head>'
                        f'<body class="{page_class}" data-root="{prefix}">'
                        f'<a class="skip" href="#content">Skip to content</a>'
                        f'<header class="topbar"><a class="brand" href="{prefix}index.html">'
                        f'<span class="mark" aria-hidden="true">f</span> fibril <small>Build. Understand. Prove.</small></a>'
                        f'<div class="controls"><button hidden class="menu-button" id="menu" aria-controls="sidebar" aria-expanded="false">Menu</button>'
                        f'<button hidden id="smaller" aria-label="Decrease reading text size">A−</button>'
                        f'<button hidden id="larger" aria-label="Increase reading text size">A+</button>'
                        f'<button hidden id="theme" aria-label="Toggle light and dark theme">Theme</button></div></header>'
                        f'<div class="progress" aria-hidden="true"></div>'
                        f'<nav class="sidebar" id="sidebar" aria-label="Book navigation">'
                        f'<div id="search-box" hidden><label class="search-label" for="search">SEARCH THE BOOK · /</label>'
                        f'<input class="search-input" id="search" type="search" placeholder="Paths, substitution, usage…" autocomplete="off">'
                        f'<div class="search-results" id="search-results" aria-live="polite"></div></div>{links}</nav>'
                        f'<main id="content" tabindex="-1"><div class="eyebrow">{badge}</div>'
                        f'<div class="reading-meta"></div><article>{body}</article></main>'
                        f'<aside class="outline" aria-label="On this page"><h2>On this page</h2><div id="outline-links"></div></aside>'
                        f'</body></html>')

    diagrams = OUT / "docs/diagrams"
    diagrams.mkdir(parents=True)
    for dot in sorted((ROOT / "docs/diagrams").glob("*.dot")):
        subprocess.run(["dot", "-Tsvg", str(dot), "-o", str(diagrams / (dot.stem + ".svg"))], check=True)
    api = ROOT / "build/docs"
    if not (api / "index.html").exists():
        raise SystemExit("Generate API reference first: make docs")
    shutil.copytree(api, OUT / "api")
    for page in pages:
        content = page.read_text()
        # Rewrite local Markdown links to the corresponding generated pages.
        def rewrite(match):
            url = match.group(1)
            if "://" in url or url.startswith("#"):
                return match.group(0)
            path, sep, fragment = url.partition("#")
            target = (page.parent / path).resolve()
            if target in destinations:
                url = relative(destinations[target], destinations[page]) + (sep + fragment if sep else "")
            return "](" + url + ")"
        content = re.sub(r"\]\(([^\s)]+)\)", rewrite, content)
        rendered = subprocess.run(["pandoc", "--from=gfm", "--to=html5"], input=content,
                                  text=True, capture_output=True, check=True).stdout
        write_page(destinations[page], titles[page], rendered)
        plain_text = html.unescape(re.sub(r"<[^>]+>", " ", rendered))
        search_index.append({"title": titles[page],
                             "url": str(destinations[page].relative_to(OUT)),
                             "text": " ".join(plain_text.split())})
    for source in sources:
        lines = source.read_text().splitlines()
        body = f'<h1>{html.escape(str(source.relative_to(ROOT)))}</h1><pre><code>'
        body += "\n".join(f'<span id="L{i}"><a href="#L{i}">{i:4}</a> {html.escape(line)}</span>'
                          for i, line in enumerate(lines, 1)) + '</code></pre>'
        write_page(destinations[source], source.stem, body)
    index = OUT / "sources.html"
    write_page(index, "Source index", '<h1>Source index</h1><ul>' + ''.join(
        f'<li><a href="{relative(destinations[p], index)}">{html.escape(str(p.relative_to(ROOT)))}</a></li>'
        for p in sources) + '</ul>')
    contents = ('<h1>Building Fibril</h1><p>A guided textbook of the implementation: '
                'theory, representations, algorithms, and evidence.</p><p>Start with '
                '<a href="docs/book/00-orientation.html">Chapter 1: Orientation</a>. '
                'Implementation chapters distinguish working prototypes from future language features.</p>')
    for part in parts:
        contents += f'<h2>{html.escape(part["title"])}</h2><ol>'
        for entry in part["pages"]:
            dest = destinations[(ROOT / entry["path"]).resolve()]
            contents += f'<li><a href="{relative(dest, OUT / "index.html")}">{html.escape(entry["title"])}</a></li>'
        contents += '</ol>'
    write_page(OUT / "index.html", "Building Fibril", contents)

    (OUT / "assets/search-data.js").write_text(
        "window.FIBRIL_SEARCH = " + json.dumps(search_index, ensure_ascii=True) + ";\n")

    class Links(HTMLParser):
        def __init__(self):
            super().__init__()
            self.urls = []
        def handle_starttag(self, tag, attrs):
            self.urls.extend(v for k, v in attrs if k in ("href", "src") and v)

    # Check handbook links (API generator owns its internal links). Fragment
    # targets are not checked yet; local file targets must exist.
    for page in OUT.rglob("*.html"):
        if (OUT / "api") in page.parents:
            continue
        parser = Links()
        parser.feed(page.read_text())
        for url in parser.urls:
            if ":" in url or url.startswith("#"):
                continue
            target = url.split("#", 1)[0]
            if target and not (page.parent / target).exists():
                raise SystemExit(f"Broken local link: {page}: {url}")
    print(f"Handbook built and local file links checked: {OUT / 'index.html'}")


if __name__ == "__main__":
    main()
