#!/usr/bin/env python3
"""Optional real-editor checks; no plugin manager, network, or compiler needed."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / "editors/vim"
EDITORS = [(name, shutil.which(name)) for name in ("nvim", "vim") if shutil.which(name)]

FIXTURE = [
    '-- TODO λ Type "quoted" ->',
    'main : IO Unit',
    r'main = putStrLn "hello -- Type \"quoted\" \\ \n \q"',
    'id : (0 A : Type 0) -> (1 x : A) -> A',
    r'id = \(0 A : Type 0) => \(1 x : A) => x',
    'λ (1 x : Bool) ⇒ if True then False else x',
    '-- keyword if in comment',
    'let (value : Unit) = () in case value of () => ()',
    '0 erased : Type 1',
    "type Type0 iffy if' True'",
    '"unterminated',
    'if True then False else True',
    '"raw\ttab"',
    '  notAHeader : Bool',
    "name' : Bool",
    "main = do",
    "do'",
]


def vim_literal(value):
    return "'" + str(value).replace("'", "''") + "'"


def point(line, needle, offset=0):
    """Vim synID columns are UTF-8 bytes, not Fibril scalar columns."""
    source = FIXTURE[line - 1]
    index = source.index(needle) + offset
    return [line, len(source[:index].encode("utf-8")) + 1]


QUERIES = [
    (point(1, "TODO"), "fibrilTodo"),
    (point(1, "Type"), "fibrilComment"),
    (point(1, '"quoted"'), "fibrilComment"),
    (point(2, "main"), "fibrilDeclaration"),
    (point(2, "IO"), "fibrilConsoleType"),
    (point(2, "Unit"), "fibrilType"),
    (point(3, "putStrLn"), "fibrilConsoleFunction"),
    (point(3, "--"), "fibrilString"),
    (point(3, "Type"), "fibrilString"),
    (point(3, '\\"'), "fibrilEscape"),
    (point(3, "quoted"), "fibrilString"),
    (point(3, "\\\\"), "fibrilEscape"),
    (point(3, "\\n"), "fibrilEscape"),
    (point(3, "\\q"), "fibrilBadEscape"),
    (point(4, "id"), "fibrilDeclaration"),
    (point(4, "(0", 1), "fibrilQuantity"),
    (point(4, "Type 0", 5), "fibrilNumber"),
    (point(4, "(1", 1), "fibrilQuantity"),
    (point(4, "->"), "fibrilOperator"),
    (point(5, "\\"), "fibrilOperator"),
    (point(5, "=>"), "fibrilOperator"),
    (point(6, "λ"), "fibrilOperator"),
    (point(6, "⇒"), "fibrilOperator"),
    (point(6, "if"), "fibrilKeyword"),
    (point(6, "True"), "fibrilBoolean"),
    (point(7, "if"), "fibrilComment"),
    (point(8, "let"), "fibrilKeyword"),
    (point(8, "case"), "fibrilKeyword"),
    (point(8, "()"), "fibrilDelimiter"),
    (point(9, "0"), "fibrilQuantity"),
    (point(9, "erased"), "fibrilDeclaration"),
    (point(10, "Type0"), ""),
    (point(10, "iffy"), ""),
    (point(10, "if'"), ""),
    (point(10, "True'"), ""),
    (point(11, "unterminated"), "fibrilString"),
    (point(12, "if"), "fibrilKeyword"),
    (point(13, "\t"), "fibrilRawControl"),
    (point(14, "notAHeader"), ""),
    (point(15, "name'"), "fibrilDeclaration"),
    (point(16, "do"), "fibrilConsoleKeyword"),
    (point(17, "do'"), ""),
]


def inspect_editor(name, executable):
    with tempfile.TemporaryDirectory() as directory:
        directory = Path(directory)
        fixture = directory / "highlight.fib"
        fixture.write_text("\n".join(FIXTURE) + "\n", encoding="utf-8")
        report = directory / "report.json"
        script = directory / "test.vim"
        script.write_text(
            "set nocompatible\nset encoding=utf-8\nset nomore\n"
            f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})\n"
            "filetype plugin on\nsyntax enable\n"
            "highlight link fibrilKeyword WarningMsg\n"
            f"execute 'edit ' . fnameescape({vim_literal(fixture)})\n"
            "syntax sync fromstart\n"
            f"let points = {json.dumps([p for p, _ in QUERIES])}\n"
            "let groups = []\n"
            "for p in points\n"
            "  call add(groups, synIDattr(synID(p[0], p[1], 1), 'name'))\n"
            "endfor\n"
            "let report = {'filetype': &filetype, 'syntax': get(b:, 'current_syntax', ''),\n"
            "\\ 'groups': groups, 'commentstring': &l:commentstring,\n"
            "\\ 'comments': &l:comments, 'apostrophe': stridx(&l:iskeyword, '39') >= 0,\n"
            "\\ 'custom_link': synIDattr(synIDtrans(hlID('fibrilKeyword')), 'name')}\n"
            "runtime syntax/fibril.vim\n"
            "runtime ftplugin/fibril.vim\n"
            "let report.reload = get(b:, 'current_syntax', '')\n"
            "execute b:undo_ftplugin\n"
            "let report.undo = &l:commentstring ==# &g:commentstring &&\n"
            "\\ &l:comments ==# &g:comments && &l:iskeyword ==# &g:iskeyword\n"
            "enew\nsetfiletype text\n"
            f"execute 'doautocmd BufRead ' . fnameescape({vim_literal(fixture)})\n"
            "let report.existing_type = &filetype\n"
            f"execute 'edit ' . fnameescape({vim_literal(directory / 'new.fib')})\n"
            "let report.new_filetype = &filetype\n"
            f"call writefile([json_encode(report)], {vim_literal(report)})\n"
            "qa!\n", encoding="utf-8")
        flags = ["--headless", "-u", "NONE", "-i", "NONE", "-n"] if name == "nvim" else [
            "-Nu", "NONE", "-i", "NONE", "-n", "-es"]
        result = subprocess.run([executable, *flags, "-S", str(script)],
                                capture_output=True, text=True, timeout=20, cwd=ROOT)
        if result.returncode or not report.exists():
            raise AssertionError(f"{name} failed ({result.returncode}): {result.stdout}\n{result.stderr}")
        return json.loads(report.read_text(encoding="utf-8"))


class EditorTests(unittest.TestCase):
    def test_runtime_in_installed_editors(self):
        if not EDITORS:
            self.skipTest("Neovim/Vim not installed")
        for name, executable in EDITORS:
            with self.subTest(editor=name):
                report = inspect_editor(name, executable)
                self.assertEqual(report["filetype"], "fibril")
                self.assertEqual(report["syntax"], "fibril")
                self.assertEqual(len(report["groups"]), len(QUERIES))
                for (position, expected), actual in zip(QUERIES, report["groups"]):
                    with self.subTest(editor=name, position=position):
                        self.assertEqual(actual, expected)
                self.assertEqual(report["commentstring"], "-- %s")
                self.assertEqual(report["comments"], ":--")
                self.assertTrue(report["apostrophe"])
                self.assertEqual(report["custom_link"], "WarningMsg")
                self.assertEqual(report["reload"], "fibril")
                self.assertTrue(report["undo"])
                self.assertEqual(report["existing_type"], "text")
                self.assertEqual(report["new_filetype"], "fibril")


if __name__ == "__main__":
    if not EDITORS:
        raise SystemExit("Optional editor tests require Neovim or Vim on PATH.")
    unittest.main()
