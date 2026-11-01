#!/usr/bin/env python3
"""Regression checks for generated textbook navigation; standard library only."""
from html.parser import HTMLParser
import json
import re
from pathlib import Path
import unittest

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
        self.assertIn('prefers-color-scheme:dark', css)

    def test_landing_page_links_every_chapter(self):
        content = (OUT / "index.html").read_text()
        for path in self.chapters:
            self.assertIn(str(path.relative_to(OUT)), content)


if __name__ == "__main__":
    unittest.main()
