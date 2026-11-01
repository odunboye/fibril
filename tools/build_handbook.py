#!/usr/bin/env python3
"""Build an offline handbook using pandoc/Graphviz, with linked source pages.

Only local project files are read; no CDN assets or network access are required.
Call graphs are curated DOT files, not inferred correctness evidence.
"""
from pathlib import Path
import html
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
    pages = sorted((ROOT / "docs").glob("*.md")) + [
        ROOT / "README.md", ROOT / "CONTRIBUTING.md",
        *sorted((ROOT / "examples").rglob("*.md")),
    ]
    sources = sorted((ROOT / "src").rglob("*.idr")) + sorted(
        (ROOT / "test/src").rglob("*.idr")) + sorted(
        (ROOT / "examples/src").rglob("*.idr"))
    destinations = {p: OUT / p.relative_to(ROOT).with_suffix(".html") for p in pages}
    destinations.update({p: OUT / "source" / (str(p.relative_to(ROOT)) + ".html")
                         for p in sources})
    nav = [("Implementation tour", OUT / "docs/implementation-tour.html"),
           ("Documentation index", OUT / "docs/README.html"),
           ("Source index", OUT / "sources.html"),
           ("API reference", OUT / "api/index.html")]
    nav += [(p.stem.replace("-", " ").title(), destinations[p]) for p in pages]
    style = """body{margin:0;font:17px/1.65 system-ui;color:#17212b;background:#fafbfc}
nav{position:fixed;box-sizing:border-box;width:260px;height:100vh;overflow:auto;padding:24px;background:#eaf0f5}
nav a{display:block;margin:7px 0}main{max-width:1000px;margin-left:280px;padding:30px}
a{color:#075ca8}pre{background:#edf1f5;padding:16px;overflow:auto}code{font-size:.9em}
img{max-width:100%;height:auto;background:white}table{border-collapse:collapse}td,th{border:1px solid #ccc;padding:8px}
@media(max-width:800px){nav{position:static;width:auto;height:auto}main{margin:0;padding:18px}}
"""

    def write_page(path, title, body):
        path.parent.mkdir(parents=True, exist_ok=True)
        links = "".join(f'<a href="{html.escape(relative(dest, path))}">{html.escape(label)}</a>'
                        for label, dest in nav)
        path.write_text(f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
                        f'<meta name="viewport" content="width=device-width,initial-scale=1">'
                        f'<title>{html.escape(title)} — Fibril</title><style>{style}</style></head>'
                        f'<body><nav><h2>Fibril handbook</h2>{links}</nav><main>{body}</main></body></html>')

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
        write_page(destinations[page], page.stem, rendered)
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
    write_page(OUT / "index.html", "Welcome", '<h1>Fibril handbook</h1><p>Start with the '
               '<a href="docs/implementation-tour.html">implementation tour</a>. '
               'This handbook separates implemented infrastructure from proposed language features.</p>')

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
