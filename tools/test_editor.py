#!/usr/bin/env python3
"""Optional real-editor checks; navigation tests also use a locally built compiler."""
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
    "message : String",
    '  (1 text : String) <- pure String "value"',
    "module Text.Greeting",
    "import Data.String",
    "export",
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
    (point(18, "String"), "fibrilType"),
    (point(19, "<-"), "fibrilOperator"),
    (point(19, "<-", 1), "fibrilOperator"),
    (point(20, "module"), "fibrilKeyword"),
    (point(20, "."), "fibrilOperator"),
    (point(21, "import"), "fibrilKeyword"),
    (point(22, "export"), "fibrilKeyword"),
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


def inspect_navigation(name, executable, line_ending="\n"):
    with tempfile.TemporaryDirectory(prefix="fibril editor ") as directory:
        directory = Path(directory)
        fixture = directory / "saved 'quoted'; input.fib"
        source = 'let (0 ignored : String) = "text 🌍e\u0301" in let (1 text : String) = "x" in text'
        fixture.write_bytes((source + line_ending).encode("utf-8"))
        origin = len(source[:source.rindex("text")].encode("utf-8")) + 1
        target = len(source[:source.index("(1 text") + 3].encode("utf-8")) + 1
        begin = source.index("(1 text") + 3
        end = source.rindex("text")
        proposed = source[:begin] + "renamed" + source[begin + 4:end] + "renamed" + source[end + 4:]
        report = directory / "navigation.json"
        invalid = directory / "invalid response"
        invalid.write_text("#!/bin/sh\nprintf '%s\\n' 'not-json'\n", encoding="utf-8")
        invalid.chmod(0o755)
        partial = json.dumps({
            "version": 1, "coordinates": "unicode-scalars;offset=0;line=1;column=1",
            "references": [
                {"start": {"line": 1, "column": 1}, "end": {"line": 1, "column": 4}},
                {"start": {"line": 99999, "column": 1}, "end": {"line": 99999, "column": 4}},
            ],
        })
        partial_script = ["#!/bin/sh", "printf '%s\\n' '" + partial + "'"]
        partial_lines = "[" + ", ".join(vim_literal(line) for line in partial_script) + "]"
        script = directory / "navigate.vim"
        script.write_text(
            "set nocompatible\nset encoding=utf-8\nset nomore\n"
            f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})\n"
            "filetype plugin on\n"
            f"let g:fibril_executable = {vim_literal(ROOT / 'build/exec/fibril')}\n"
            f"execute 'edit ' . fnameescape({vim_literal(fixture)})\n"
            "let report = {'command': exists(':FibrilDefinition'),\n"
            "\\ 'plug': !empty(maparg('<Plug>(FibrilDefinition)', 'n')),\n"
            "\\ 'gd': maparg('gd', 'n')}\n"
            f"call cursor(1, {origin})\n"
            "let report.success = fibril#definition()\n"
            "let report.target = col('.')\n"
            f"call cursor(1, {origin})\n"
            "FibrilDefinition\n"
            "let report.command_target = col('.')\n"
            f"call cursor(1, {origin})\n"
            "let rename_window = win_getid()\n"
            f"let rename_disk = readfile({vim_literal(fixture)}, 'b')\n"
            "let report.rename_success = fibril#rename_preview('renamed')\n"
            "let report.rename_lines = getline(1, '$')\n"
            "let report.rename_readonly = &readonly && !&modifiable && &buftype ==# 'nofile' && &filetype ==# 'diff'\n"
            "close\n"
            "let report.rename_source_unmodified = !&modified\n"
            f"let report.rename_disk_unchanged = readfile({vim_literal(fixture)}, 'b') ==# rename_disk\n"
            f"let report.rename_source_unchanged = getline(1) ==# {vim_literal(source)}\n"
            "let report.rename_source_cursor = col('.')\n"
            "FibrilRenamePreview renamed\n"
            "let report.rename_command = &buftype ==# 'nofile'\n"
            "close\n"
            "let report.rename_noop = fibril#rename_preview('text')\n"
            "let report.rename_keyword = fibril#rename_preview('Bool')\n"
            "let report.rename_rejection_window = win_getid() == rename_window\n"
            f"call cursor(1, {origin})\n"
            "let source_window = win_getid()\n"
            "let report.reference_success = fibril#references()\n"
            "let report.reference_window = getwininfo(win_getid())[0].loclist\n"
            "call win_gotoid(source_window)\n"
            "let report.reference_items = getloclist(0)\n"
            "let report.reference_origin = col('.')\n"
            "lclose\n"
            "FibrilReferences\n"
            "call win_gotoid(source_window)\n"
            "let reference_id = getloclist(0, {'id': 0}).id\n"
            "lclose\n"
            "call cursor(1, 1)\n"
            "let report.miss = fibril#definition()\n"
            "let report.miss_position = col('.')\n"
            "let report.reference_miss = fibril#references()\n"
            "let report.reference_preserved_miss = getloclist(0, {'id': 0}).id == reference_id\n"
            "call setline(1, getline(1) . ' ')\n"
            "let report.modified = fibril#definition()\n"
            "let report.reference_modified = fibril#references()\n"
            "let report.rename_modified = fibril#rename_preview('renamed')\n"
            "edit!\n"
            f"let saved_disk = readfile({vim_literal(fixture)}, 'b')\n"
            f"call writefile(['different disk contents'], {vim_literal(fixture)})\n"
            "let report.stale = fibril#definition()\n"
            "let report.reference_stale = fibril#references()\n"
            f"call writefile(saved_disk, {vim_literal(fixture)}, 'b')\n"
            "let g:fibril_executable = '/nonexistent/fibril'\n"
            "let report.missing = fibril#definition()\n"
            f"let g:fibril_executable = {vim_literal(invalid)}\n"
            "let report.invalid = fibril#definition()\n"
            "let report.reference_invalid = fibril#references()\n"
            "let report.rename_invalid = fibril#rename_preview('renamed')\n"
            f"call writefile({partial_lines}, {vim_literal(invalid)})\n"
            "let report.reference_partial = fibril#references()\n"
            "let report.reference_preserved_error = getloclist(0, {'id': 0}).id == reference_id\n"
            "execute b:undo_ftplugin\n"
            "let report.undo_command = exists(':FibrilDefinition')\n"
            "let report.undo_reference_command = exists(':FibrilReferences')\n"
            "let report.undo_rename_command = exists(':FibrilRenamePreview')\n"
            "let report.undo_rename_plug = maparg('<Plug>(FibrilRenamePreview)', 'n')\n"
            "let report.undo_reference_plug = maparg('<Plug>(FibrilReferences)', 'n')\n"
            "let report.undo_plug = maparg('<Plug>(FibrilDefinition)', 'n')\n"
            f"call writefile([json_encode(report)], {vim_literal(report)})\n"
            "qa!\n", encoding="utf-8")
        flags = ["--headless", "-u", "NONE", "-i", "NONE", "-n"] if name == "nvim" else [
            "-Nu", "NONE", "-i", "NONE", "-n", "-es"]
        result = subprocess.run([executable, *flags, "-S", str(script)],
                                capture_output=True, text=True, timeout=30, cwd=ROOT)
        if result.returncode or not report.exists():
            raise AssertionError(f"{name} navigation failed: {result.stdout}\n{result.stderr}")
        data = json.loads(report.read_text(encoding="utf-8"))
        data["expected_rename_line"] = "+" + proposed
        return data, target


def inspect_checking(name, executable, line_ending="\n"):
    with tempfile.TemporaryDirectory(prefix="fibril check ") as directory:
        directory = Path(directory)
        sources = {
            "located": 'main : String\nmain = let (0 ignored : String) = "🌍e\u0301" in missing\n',
            "core": '(True : String)\n',
            "resource": '(\\(1 x : Bool) => False) True\n',
            "eof": 'main : Bool\nmain =\n',
            "bom": "\ufeffTrue\n",
            "accepted": 'main : IO Unit\nmain = putStrLn "must not execute"\n',
        }
        paths = {}
        for label, source in sources.items():
            path = directory / (label + " 'quoted'.fib")
            path.write_bytes(source.replace("\n", line_ending).encode("utf-8"))
            paths[label] = path
        invalid = directory / "invalid compiler"
        invalid.write_text("#!/bin/sh\nprintf '%s\\n' 'invalid-json'\nexit 1\n", encoding="utf-8")
        invalid.chmod(0o755)
        report = directory / "checking.json"
        script = directory / "check.vim"
        commands = [
            "set nocompatible", "set encoding=utf-8", "set nomore",
            f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})",
            "filetype plugin on",
            f"let g:fibril_executable = {vim_literal(ROOT / 'build/exec/fibril')}",
            "let report = {}",
        ]
        for label, path in paths.items():
            commands += [
                f"execute 'edit ' . fnameescape({vim_literal(path)})",
                "call cursor(1, 2)", "let source_window = win_getid()",
                "let source_position = getpos('.')",
                f"let handled = fibril#check()",
                "let opened = win_getid() != source_window",
                "call win_gotoid(source_window)",
                f"let report.{label} = {{'handled': handled, 'opened': opened, 'items': getloclist(0),",
                "\\ 'unchanged': getpos('.') == source_position && !&modified}",
            ]
            if label != "accepted":
                commands += ["lclose"]
        commands += [
            "FibrilCheck",
            "let report.check_command = empty(getloclist(0))",
            "let report.check_plug = !empty(maparg('<Plug>(FibrilCheck)', 'n'))",
            "let previous_list = getloclist(0, {'id': 0}).id",
            "call setline(1, getline(1) . ' ')",
            "let report.modified = fibril#check()", "edit!",
            f"let g:fibril_executable = {vim_literal(invalid)}",
            "let report.invalid = fibril#check()",
            "let report.preserved = getloclist(0, {'id': 0}).id == previous_list",
            "let report.no_extra_window = winnr('$') == 1",
        ]
        diagnostic = {"severity": "error", "stage": "runtime-checking", "message": "test",
                      "position": None, "byteOffset": None}
        envelope = {"version": 1, "coordinates": "unicode-scalars;offset=0;line=1;column=1"}
        faults = [
            ({**envelope, "version": 2, "accepted": True, "report": [], "diagnostics": []}, 0),
            ({**envelope, "accepted": True, "report": [], "diagnostics": []}, 1),
            ({**envelope, "accepted": False, "report": [], "diagnostics": [diagnostic]}, 0),
            ({**envelope, "accepted": False, "report": [], "diagnostics": [
                {**diagnostic, "position": {"offset": 0, "line": 1, "column": 1}},
                {**diagnostic, "position": {"offset": 0, "line": 999, "column": 1}},
            ]}, 1),
            ({**envelope, "accepted": False, "report": [], "diagnostics": [
                {**diagnostic, "position": {"offset": 1, "line": 1, "column": 1}},
            ]}, 1),
        ]
        commands += ["let report.faults = []"]
        for payload, status in faults:
            shell_lines = ["#!/bin/sh", "printf '%s\\n' '" + json.dumps(payload) + "'", f"exit {status}"]
            literal = "[" + ", ".join(vim_literal(line) for line in shell_lines) + "]"
            commands += [
                f"call writefile({literal}, {vim_literal(invalid)})",
                "let handled = fibril#check()",
                "call add(report.faults, handled == 0 && getloclist(0, {'id': 0}).id == previous_list && winnr('$') == 1)",
            ]
        payload = {**envelope, "accepted": False, "report": [], "diagnostics": [
            {**diagnostic, "stage": "decoding", "byteOffset": 4}]}
        shell_lines = ["#!/bin/sh", "printf '%s\\n' '" + json.dumps(payload) + "'", "exit 1"]
        literal = "[" + ", ".join(vim_literal(line) for line in shell_lines) + "]"
        commands += [
            f"call writefile({literal}, {vim_literal(invalid)})",
            "let report.byte_handled = fibril#check()",
            "call win_gotoid(source_window)",
            "let report.byte_item = getloclist(0)[0]",
            "lclose",
            "let report.messages = execute('messages')",
            "execute b:undo_ftplugin",
            "let report.undo_command = exists(':FibrilCheck')",
            "let report.undo_plug = maparg('<Plug>(FibrilCheck)', 'n')",
            f"call writefile([json_encode(report)], {vim_literal(report)})",
            "qa!",
        ]
        script.write_text("\n".join(commands) + "\n", encoding="utf-8")
        flags = ["--headless", "-u", "NONE", "-i", "NONE", "-n"] if name == "nvim" else [
            "-Nu", "NONE", "-i", "NONE", "-n", "-es"]
        result = subprocess.run([executable, *flags, "-S", str(script)],
                                capture_output=True, text=True, timeout=30, cwd=ROOT)
        if result.returncode or not report.exists():
            raise AssertionError(f"{name} checking failed: {result.stdout}\n{result.stderr}")
        data = json.loads(report.read_text(encoding="utf-8"))
        for label, path in paths.items():
            assert path.read_bytes() == sources[label].replace("\n", line_ending).encode("utf-8")
        data["expected_column"] = len(sources["located"].splitlines()[1].split("missing")[0].encode("utf-8")) + 1
        return data


class EditorTests(unittest.TestCase):
    def test_checking_in_installed_editors(self):
        if not (ROOT / "build/exec/fibril").exists():
            self.skipTest("build Fibril first to test optional checking")
        for name, executable in EDITORS:
            for line_ending in ("\n", "\r\n"):
                with self.subTest(editor=name, line_ending=line_ending):
                    report = inspect_checking(name, executable, line_ending)
                    for label in ("located", "core", "resource", "eof", "bom", "accepted"):
                        self.assertEqual(report[label]["handled"], 1, label)
                        self.assertTrue(report[label]["unchanged"], label)
                    item = report["located"]["items"][0]
                    self.assertEqual(item["lnum"], 2)
                    self.assertEqual(item["col"], report["expected_column"])
                    self.assertEqual(item["valid"], 1)
                    for label in ("core", "resource", "eof", "bom"):
                        item = report[label]["items"][0]
                        self.assertEqual(item["lnum"], 0)
                        self.assertEqual(item["col"], 0)
                        self.assertEqual(item["valid"], 0)
                    self.assertIn("unlocated", report["core"]["items"][0]["text"])
                    self.assertIn("EOF", report["eof"]["items"][0]["text"])
                    self.assertEqual(report["accepted"]["items"], [])
                    self.assertFalse(report["accepted"]["opened"])
                    self.assertIn("byte-order mark", report["bom"]["items"][0]["text"])
                    for label in ("located", "core", "resource", "eof", "bom"):
                        self.assertTrue(report[label]["opened"])
                    self.assertEqual(report["modified"], 0)
                    self.assertEqual(report["invalid"], 0)
                    self.assertTrue(report["preserved"])
                    self.assertTrue(report["no_extra_window"])
                    self.assertTrue(report["check_command"])
                    self.assertTrue(report["check_plug"])
                    self.assertTrue(all(report["faults"]))
                    self.assertEqual(report["byte_handled"], 1)
                    self.assertEqual(report["byte_item"]["valid"], 0)
                    self.assertEqual(report["byte_item"]["lnum"], 0)
                    self.assertIn("byte offset 4", report["byte_item"]["text"])
                    self.assertNotIn("must not execute", report["messages"])
                    self.assertEqual(report["undo_command"], 0)
                    self.assertEqual(report["undo_plug"], "")

    def test_navigation_in_installed_editors(self):
        if not (ROOT / "build/exec/fibril").exists():
            self.skipTest("build Fibril first to test optional CLI navigation")
        for name, executable in EDITORS:
            for line_ending in ("\n", "\r\n"):
                with self.subTest(editor=name, line_ending=line_ending):
                    report, target = inspect_navigation(name, executable, line_ending)
                    self.assertEqual(report["command"], 2)
                    self.assertTrue(report["plug"])
                    self.assertEqual(report["gd"], "")
                    self.assertEqual(report["success"], 1)
                    self.assertEqual(report["target"], target)
                    self.assertEqual(report["command_target"], target)
                    self.assertEqual(report["miss"], 0)
                    self.assertEqual(report["miss_position"], 1)
                    for field in ("modified", "stale", "missing", "invalid"):
                        self.assertEqual(report[field], 0, field)
                    self.assertEqual(report["undo_command"], 0)
                    self.assertEqual(report["undo_plug"], "")
                    self.assertEqual(report["reference_success"], 1)
                    self.assertEqual(report["reference_window"], 1)
                    self.assertEqual(len(report["reference_items"]), 2)
                    self.assertEqual(report["reference_items"][0]["col"], target)
                    self.assertEqual(report["reference_items"][0]["end_col"], target + 3)
                    self.assertEqual(report["reference_origin"], report["reference_items"][1]["col"])
                    for field in ("reference_miss", "reference_modified", "reference_stale", "reference_invalid", "reference_partial"):
                        self.assertEqual(report[field], 0, field)
                    self.assertTrue(report["reference_preserved_miss"])
                    self.assertTrue(report["reference_preserved_error"])
                    self.assertEqual(report["undo_reference_command"], 0)
                    self.assertEqual(report["undo_reference_plug"], "")
                    self.assertEqual(report["rename_success"], 1)
                    self.assertIn(report["expected_rename_line"], report["rename_lines"])
                    self.assertTrue(report["rename_readonly"])
                    self.assertTrue(report["rename_source_unmodified"])
                    self.assertTrue(report["rename_disk_unchanged"])
                    self.assertTrue(report["rename_source_unchanged"])
                    self.assertEqual(report["rename_source_cursor"], report["reference_origin"])
                    self.assertTrue(report["rename_command"])
                    self.assertTrue(report["rename_rejection_window"])
                    for field in ("rename_noop", "rename_keyword", "rename_modified", "rename_invalid"):
                        self.assertEqual(report[field], 0, field)
                    self.assertEqual(report["undo_rename_command"], 0)
                    self.assertEqual(report["undo_rename_plug"], "")

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
