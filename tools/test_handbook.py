#!/usr/bin/env python3
"""Regression checks for generated textbook navigation; standard library only."""
from html.parser import HTMLParser
import json
import hashlib
import re
from pathlib import Path
import unittest
import build_handbook
import serve_handbook
import threading
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build/handbook"


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__()
        self.current = []
        self.footer_links = []
        self.in_footer = False
        self.feed(path.read_text())

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "footer":
            self.in_footer = True
        if tag == "a" and "aria-current" in attrs:
            self.current.append(attrs["href"])
        if tag == "a" and self.in_footer:
            self.footer_links.append(attrs["href"])

    def handle_endtag(self, tag):
        if tag == "footer":
            self.in_footer = False


class Code(HTMLParser):
    """Read source code without line-number labels; detect unescaped markup."""
    def __init__(self, fragment):
        super().__init__()
        self.inside = False
        self.line_number = False
        self.text = []
        self.ids = []
        self.scripts = []
        self.feed(fragment)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "code":
            self.inside = True
        if "id" in attrs:
            self.ids.append(attrs["id"])
        if tag == "a" and "line-number" in attrs.get("class", "").split():
            self.line_number = True
        if tag == "script":
            self.scripts.append(attrs)

    def handle_endtag(self, tag):
        if tag == "code":
            self.inside = False
        if tag == "a":
            self.line_number = False

    def handle_data(self, data):
        if self.inside and not self.line_number:
            self.text.append(data)

    def source_lines(self):
        return [line.removeprefix(" ") for line in "".join(self.text).splitlines()]


class TextbookTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parts = json.loads((ROOT / "docs/book.json").read_text())
        cls.chapters = [OUT / Path(e["path"]).with_suffix(".html")
                        for e in parts[0]["pages"]]

    def test_all_chapters_have_one_current_page(self):
        for path in self.chapters:
            with self.subTest(page=path):
                page = Page(path)
                self.assertEqual(len(page.current), 1)
                self.assertEqual((path.parent / page.current[0]).resolve(), path.resolve())

    def test_previous_and_next_follow_manifest(self):
        for i, path in enumerate(self.chapters):
            with self.subTest(page=path):
                expected = [self.chapters[i - 1] if i else OUT / "index.html",
                            self.chapters[i + 1] if i + 1 < len(self.chapters)
                            else OUT / "docs/references.html"]
                links = Page(path).footer_links
                self.assertEqual(len(links), 2)
                self.assertEqual([(path.parent / link).resolve() for link in links],
                                 [p.resolve() for p in expected])

    def test_reading_assets_are_local_and_present(self):
        for name in ("book.css", "book.js", "search-data.js"):
            self.assertTrue((OUT / "assets" / name).is_file())
        for path in self.chapters:
            content = path.read_text()
            self.assertIn('class="skip"', content)
            self.assertIn('aria-label="Book navigation"', content)
            self.assertIn('id="search"', content)
            self.assertIn('id="outline-links"', content)

    def test_search_index_contains_every_chapter(self):
        script = (OUT / "assets/search-data.js").read_text()
        prefix = "window.FIBRIL_SEARCH = "
        self.assertTrue(script.startswith(prefix))
        entries = json.loads(script[len(prefix):].strip().removesuffix(";"))
        urls = {entry["url"] for entry in entries}
        for path in self.chapters:
            self.assertIn(str(path.relative_to(OUT)), urls)
        self.assertTrue(all(entry["title"] and entry["text"] for entry in entries))

    def test_typography_separates_prose_ui_and_code(self):
        css = (OUT / "assets/book.css").read_text()
        for declaration in ('--font-reading:', '--font-ui:', '--font-code:',
                            '--reading-size:20px', 'max-width:66ch',
                            'font-variant-ligatures:none', 'text-wrap:balance'):
            self.assertIn(declaration, css)
        self.assertNotIn('@import', css)

    def test_bundled_hyperlegible_fonts_and_licenses(self):
        directory = OUT / "assets/fonts"
        manifest = json.loads((directory / "manifest.json").read_text())
        css = (OUT / "assets/book.css").read_text()
        self.assertEqual(len(manifest["files"]), 4)
        for name, expected in manifest["files"].items():
            data = (directory / name).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), expected)
            self.assertEqual(data[:4], bytes([0, 1, 0, 0]))
            self.assertIn('fonts/' + name, css)
        for source in manifest["sources"]:
            license_text = (directory / source["license_file"]).read_text()
            self.assertIn("SIL OPEN FONT LICENSE Version 1.1", license_text)
            self.assertIn("Copyright", license_text)
        self.assertIn('"Atkinson Hyperlegible Next"', css)
        self.assertIn('"Atkinson Hyperlegible Mono"', css)

    def test_theme_control_has_accessible_sun_icon(self):
        content = self.chapters[0].read_text()
        self.assertIn('id="theme" aria-label="Toggle light and dark theme"', content)
        self.assertIn('<svg class="theme-icon"', content)
        self.assertIn('aria-hidden="true" focusable="false"', content)
        self.assertNotIn('>Theme</button>', content)

    def test_reading_palette_has_accessible_contrast(self):
        css = (OUT / "assets/book.css").read_text()

        def luminance(color):
            channels = [int(color[i:i + 2], 16) / 255 for i in (0, 2, 4)]
            linear = [v / 12.92 if v <= 0.04045 else ((v + 0.055) / 1.055) ** 2.4
                      for v in channels]
            return sum(v * weight for v, weight in zip(linear, (0.2126, 0.7152, 0.0722)))

        def contrast(a, b):
            bright, dark = sorted((luminance(a), luminance(b)), reverse=True)
            return (bright + 0.05) / (dark + 0.05)

        for selector in (':root', ':root[data-theme=dark]'):
            match = re.search(re.escape(selector) + r'\s*\{([^}]+)\}', css)
            self.assertIsNotNone(match)
            palette = dict(re.findall(r'--([a-z-]+):\s*#([0-9a-fA-F]{6});', match.group(1)))
            for surface in ('paper', 'panel', 'code'):
                with self.subTest(theme=selector, surface=surface):
                    self.assertGreaterEqual(contrast(palette['ink'], palette[surface]), 7)
                    self.assertGreaterEqual(contrast(palette['muted'], palette[surface]), 4.5)
                    self.assertGreaterEqual(contrast(palette['accent'], palette[surface]), 4.5)
            for token in ("keyword", "type", "string", "number", "comment", "function", "error"):
                with self.subTest(theme=selector, token=token):
                    self.assertGreaterEqual(contrast(palette["syntax-" + token], palette["code"]), 4.5)
        self.assertIn('prefers-color-scheme:dark', css)

    def test_idris_and_fibril_source_pages_are_highlighted(self):
        cases = [
            ("examples/core/hello-world.fib", "fibril"),
            ("src/Fibril/Core/Term.idr", "idris"),
        ]
        for path, language in cases:
            with self.subTest(path=path):
                rendered = (OUT / "source" / (path + ".html")).read_text()
                self.assertIn(f'class="sourceCode {language}"', rendered)
                self.assertRegex(rendered, r'<span class="(?:kw|dt|st)">')
                count = len((ROOT / path).read_text().splitlines())
                self.assertEqual(re.findall(r'\bid="L(\d+)"', rendered),
                                 [str(n) for n in range(1, count + 1)])
                self.assertIn('href="#L1"', rendered)

    def test_fenced_examples_have_both_languages(self):
        fibril = (OUT / "docs/console-runner.html").read_text()
        idris = (OUT / "docs/book/01-binding.html").read_text()
        self.assertIn('class="sourceCode fibril"', fibril)
        self.assertIn('<span class="st">', fibril)
        self.assertIn('class="sourceCode idris"', idris)
        self.assertIn('<span class="dt">', idris)

    def test_highlighted_source_preserves_text_anchors_and_escaping(self):
        samples = [
            'main : IO Unit\nmain = putStrLn "<script> & \\"quoted\\""\n\n',
            '-- fence follows\n~~~~~~~~\n<script>not executable</script>\n',
            '\n\n',
            'main\n  \n\t\n',
            '',
        ]
        for suffix in (".fib", ".idr"):
            for text in samples:
                with self.subTest(suffix=suffix, text=text):
                    rendered = build_handbook.render_source(ROOT / ("sample" + suffix), text)
                    code = Code(rendered)
                    self.assertEqual(code.source_lines(), text.splitlines())
                    self.assertEqual([i for i in code.ids if re.fullmatch(r"L\d+", i)],
                                     [f"L{i}" for i in range(1, len(text.splitlines()) + 1)])
                    self.assertFalse(code.scripts)

    def test_fibril_grammar_handles_keywords_comments_and_escapes(self):
        rendered = build_handbook.render_markdown(
            '```fib\nif True then putStrLn "-- Type\\n\\q" else False\n'
            "-- comment\nif' Type0\nmain = do\n```\n")
        self.assertIn('<span class="kw">if</span>', rendered)
        self.assertIn('<span class="co">-- comment</span>', rendered)
        self.assertIn('<span class="kw">do</span>', rendered)
        self.assertIn('<span class="sc">\\n</span>', rendered)
        self.assertIn('<span class="er">\\q</span>', rendered)
        self.assertNotIn('<span class="kw">if</span>\'', rendered)

    def test_presentation_asset_urls_use_content_hashes(self):
        content = self.chapters[0].read_text()
        for name in ("book.css", "book.js"):
            digest = hashlib.sha256((OUT / "assets" / name).read_bytes()).hexdigest()[:12]
            self.assertIn(f"assets/{name}?v={digest}", content)

    def test_local_server_revalidates_html_and_styles(self):
        with serve_handbook.make_server(port=0) as server:
            thread = threading.Thread(target=server.serve_forever,
                                      kwargs={"poll_interval": 0.05}, daemon=True)
            thread.start()
            try:
                for path in ("/index.html", "/assets/book.css?v=test"):
                    url = f"http://127.0.0.1:{server.server_address[1]}{path}"
                    with urlopen(url, timeout=5) as response:
                        self.assertEqual(response.status, 200)
                        self.assertEqual(response.headers["Cache-Control"], "no-cache")
                        self.assertTrue(response.read())
            finally:
                server.shutdown()
                thread.join(timeout=5)
            self.assertFalse(thread.is_alive())

    def test_landing_page_links_every_chapter(self):
        content = (OUT / "index.html").read_text()
        for path in self.chapters:
            self.assertIn(str(path.relative_to(OUT)), content)


if __name__ == "__main__":
    unittest.main()
