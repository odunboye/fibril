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
    "keep : {0 A : Type} -> (1 value : A) -> A",
    'main = keep {String} "hello"',
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
    (point(23, "{"), "fibrilDelimiter"),
    (point(23, "0 A"), "fibrilQuantity"),
    (point(24, "{"), "fibrilDelimiter"),
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


def inspect_project_checking(name, executable, line_ending):
    import shlex
    with tempfile.TemporaryDirectory(prefix="fibril project 'quoted' ") as directory:
        directory = Path(directory)
        entry = directory / "Main.fib"
        dependency = directory / "Library.fib"
        entry_source = "module Main\nimport Library\nmain : IO Unit\nmain = Library.output\n"
        bad_source = ('module Library\nexport\noutput : IO Unit\n'
                      'output = let (0 ignored : String) = "🌍e\u0301" in missing\n')
        valid_source = 'module Library\nexport\noutput : IO Unit\noutput = putStrLn "must not execute"\n'
        entry.write_bytes(entry_source.replace("\n", line_ending).encode())
        dependency.write_bytes(bad_source.replace("\n", line_ending).encode())
        binary = ROOT / "build/exec/fibril"
        outcome = subprocess.run(
            [str(binary), "check", "--json", "--source-dir", str(directory), str(entry)],
            capture_output=True, text=True, check=False)
        envelope = json.loads(outcome.stdout)
        fake = directory / "fake compiler"
        fake.write_text("#!/bin/sh\nexit 2\n")
        fake.chmod(0o755)
        faults = [
            {**envelope, "version": 1},
            {**envelope, "sources": []},
            {**envelope, "diagnostics": envelope["diagnostics"] + [{"path": 0}]},
            {**envelope, "diagnostics": [{**envelope["diagnostics"][0],
                "position": {"offset": 1, "line": 1, "column": 1}}]},
            {**envelope, "sources": [
                {**source, "text": source["text"] + " "} for source in envelope["sources"]]},
            {**envelope, "root": str(directory / "other")},
        ]
        result_path = directory / "report.json"
        commands = [
            "set nocompatible", "set encoding=utf-8", "set nomore", "set hidden",
            f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})",
            "filetype plugin on",
            f"let g:fibril_executable = {vim_literal(binary)}",
            f"let g:fibril_source_dir = {vim_literal(directory)}",
            f"execute 'edit ' . fnameescape({vim_literal(entry)})",
            "let source_window = win_getid()", "let entry_buffer = bufnr('%')", "let report = {}",
            "let report.unloaded = fibril#check_project(g:fibril_source_dir)",
            "call win_gotoid(source_window)",
            "let report.unloaded_item = getloclist(0)[0]", "lclose",
            f"let report.not_loaded = !bufloaded({vim_literal(dependency)})",
            f"execute 'edit ' . fnameescape({vim_literal(dependency)})",
            "let dependency_buffer = bufnr('%')",
            "execute 'buffer ' . entry_buffer",
            "call cursor(2, 3)", "let position = getpos('.')",
            "FibrilCheckProject", "call win_gotoid(source_window)",
            "let report.loaded_item = getloclist(0)[0]",
            "let report.correct_buffer = report.loaded_item.bufnr == dependency_buffer",
            "let report.unchanged = getpos('.') == position && !&modified",
            "lclose", "lfirst",
            "let report.jumped = bufnr('%') == dependency_buffer && line('.') == 4 && col('.') == report.loaded_item.col",
            "execute 'buffer ' . entry_buffer",
            "let previous_list = getloclist(0, {'id': 0}).id",
            "let saved_line = getbufline(dependency_buffer, 4)[0]",
            "call setbufline(dependency_buffer, 4, saved_line . ' ')",
            "let report.modified = fibril#check_project(g:fibril_source_dir)",
            "let report.preserved = getloclist(0, {'id': 0}).id == previous_list",
            "call setbufline(dependency_buffer, 4, saved_line)",
            "call setbufvar(dependency_buffer, '&modified', 0)",
            f"let g:fibril_executable = {vim_literal(fake)}",
            "let report.faults = []",
        ]
        for payload in faults:
            shell = ["#!/bin/sh", "printf '%s\\n' " + shlex.quote(json.dumps(payload)), "exit 1"]
            commands += [
                f"call writefile([{', '.join(vim_literal(x) for x in shell)}], {vim_literal(fake)})",
                "let handled = fibril#check_project(g:fibril_source_dir)",
                "call add(report.faults, handled == 0 && getloclist(0, {'id': 0}).id == previous_list && winnr('$') == 1)",
            ]
        # Simulate a dependency changing while the compiler handles the request.
        shell = ["#!/bin/sh", "printf ' ' >> " + shlex.quote(str(dependency)),
                 "printf '%s\\n' " + shlex.quote(json.dumps(envelope)), "exit 1"]
        commands += [
            f"call writefile([{', '.join(vim_literal(x) for x in shell)}], {vim_literal(fake)})",
            "let report.stale = fibril#check_project(g:fibril_source_dir)",
            "let report.stale_preserved = getloclist(0, {'id': 0}).id == previous_list",
        ]
        unavailable = {**envelope, "root": None, "sources": [], "diagnostics": [{
            **envelope["diagnostics"][0], "sourceAvailable": False, "position": None,
            "byteOffset": 4, "stage": "decoding"}]}
        shell = ["#!/bin/sh", "printf '%s\\n' " + shlex.quote(json.dumps(unavailable)), "exit 1"]
        commands += [
            f"call writefile([{', '.join(vim_literal(x) for x in shell)}], {vim_literal(fake)})",
            "let report.unavailable = fibril#check_project(g:fibril_source_dir)",
            "call win_gotoid(source_window)",
            "let report.unavailable_item = getloclist(0)[0]", "lclose",
        ]
        valid = directory / "valid.template"
        valid.write_bytes(valid_source.replace("\n", line_ending).encode())
        commands += [
            f"call writefile(readfile({vim_literal(valid)}, 'b'), {vim_literal(dependency)}, 'b')",
            "execute 'buffer ' . dependency_buffer", "edit!",
            "execute 'buffer ' . entry_buffer",
            f"let g:fibril_executable = {vim_literal(binary)}",
            "let report.accepted = fibril#check_project(g:fibril_source_dir)",
            "let report.accepted_items = getloclist(0)",
            "let report.no_extra_window = winnr('$') == 1",
            "call cursor(3, 8)",
            "let report.builtin_help = fibril#definition()",
            "let report.builtin_buffer = &buftype ==# 'nofile' && &readonly && !&modifiable && getline(1) ==# 'Built-in reference: IO'",
            "close",
            "execute 'buffer ' . dependency_buffer", "call cursor(4, 10)",
            "let report.prelude_help = fibril#reference()",
            "let report.prelude_buffer = &buftype ==# 'nofile' && &readonly && !&modifiable && getline('.') =~# '^putStrLn = '",
            "close", "execute 'buffer ' . entry_buffer",
            f"let g:fibril_project_entry = {vim_literal(entry)}",
            "call cursor(4, 16)", "let original_position = getpos('.')",
            "execute 'bunload ' . dependency_buffer",
            "let saved_encodings = &fileencodings", "set fileencodings=latin1,utf-8",
            "let report.definition_unloaded = fibril#definition_project(g:fibril_source_dir, g:fibril_project_entry)",
            "let &fileencodings = saved_encodings",
            "let report.definition_auto = resolve(expand('%:p')) ==# resolve(fnamemodify(bufname(dependency_buffer), ':p')) && line('.') == 4 && col('.') == 1",
            "execute 'buffer ' . dependency_buffer", "execute 'buffer ' . entry_buffer",
            "call cursor(4, 16)",
            "call setbufline(dependency_buffer, 4, getbufline(dependency_buffer, 4)[0] . ' ')",
            "let report.definition_modified = fibril#definition_project(g:fibril_source_dir, g:fibril_project_entry)",
            "execute 'buffer! ' . dependency_buffer", "edit!",
            "execute 'buffer ' . entry_buffer",
            "call cursor(4, 16)", "FibrilDefinitionProject",
            "let report.definition_jump = resolve(expand('%:p')) ==# resolve(fnamemodify(bufname(dependency_buffer), ':p')) && line('.') == 4 && col('.') == 1",
            "call cursor(3, 1)", "FibrilDefinitionProject",
            "let report.library_definition = resolve(expand('%:p')) ==# resolve(fnamemodify(bufname(dependency_buffer), ':p')) && line('.') == 4 && col('.') == 1",
            "execute 'buffer ' . entry_buffer",
            "for info in getbufinfo({'bufloaded': 1})",
            "  if resolve(fnamemodify(info.name, ':p')) ==# resolve(fnamemodify(bufname(dependency_buffer), ':p'))",
            "    execute 'bunload ' . info.bufnr",
            "  endif",
            "endfor",
            "augroup FibrilTestReadHook", "autocmd!",
            "autocmd BufReadPost *.fib call setline(4, getline(4) . ' ') | call cursor(1, 1)",
            "augroup END",
            "call cursor(4, 16)",
            "let report.read_hook_refused = fibril#definition_project(g:fibril_source_dir, g:fibril_project_entry)",
            "let report.read_hook_preserved = getline(4) =~# ' $'",
            "augroup FibrilTestReadHook", "autocmd!", "augroup END", "edit!",
            "let report.definition_plug = !empty(maparg('<Plug>(FibrilDefinitionProject)', 'n'))",
            "let report.plug = !empty(maparg('<Plug>(FibrilCheckProject)', 'n'))",
            "let report.messages = execute('messages')",
            "execute b:undo_ftplugin",
            "let report.definition_undo_command = exists(':FibrilDefinitionProject')",
            "let report.definition_undo_plug = maparg('<Plug>(FibrilDefinitionProject)', 'n')",
            "let report.undo_command = exists(':FibrilCheckProject')",
            "let report.undo_plug = maparg('<Plug>(FibrilCheckProject)', 'n')",
            f"call writefile([json_encode(report)], {vim_literal(result_path)})",
            "qa!",
        ]
        # Insert malformed definition packets before final messages/undo capture.
        location = {"path": str(dependency.resolve()), "range": {
            "start": {"offset": 0, "line": 1, "column": 1},
            "end": {"offset": 6, "line": 1, "column": 7}}}
        definition_packet = {**envelope, "checked": True, "query": str(dependency.resolve()),
            "sources": [{"path": str(p.resolve()), "text": text.replace("\n", line_ending)}
                        for p, text in ((entry, entry_source), (dependency, valid_source))],
            "definition": location}
        bad_packets = [
            {**definition_packet, "query": str(entry.resolve())},
            {**definition_packet, "definition": {**location, "path": str(directory / "outside.fib")}},
            {**definition_packet, "definition": {**location, "range": {
                **location["range"], "end": {"offset": 0, "line": 1, "column": 1}}}},
            {**definition_packet, "sources": []},
        ]
        extra = [f"let g:fibril_executable = {vim_literal(fake)}",
                 "let report.definition_faults = []", "let previous_position = getpos('.')",
                 "let previous_buffer = bufnr('%')", "let previous_list = getloclist(0, {'id': 0}).id"]
        for payload in bad_packets:
            shell = ["#!/bin/sh", "printf '%s\\n' " + shlex.quote(json.dumps(payload)), "exit 0"]
            extra += [
                f"call writefile([{', '.join(vim_literal(x) for x in shell)}], {vim_literal(fake)})",
                "let handled = fibril#definition_project(g:fibril_source_dir, g:fibril_project_entry)",
                "call add(report.definition_faults, handled == 0 && bufnr('%') == previous_buffer && getpos('.') == previous_position && getloclist(0, {'id': 0}).id == previous_list)",
            ]
        insertion = commands.index("let report.messages = execute('messages')")
        commands[insertion:insertion] = extra
        script = directory / "project.vim"
        script.write_text("\n".join(commands) + "\n")
        flags = ["--headless", "-u", "NONE", "-i", "NONE", "-n"] if name == "nvim" else [
            "-Nu", "NONE", "-i", "NONE", "-n", "-es"]
        result = subprocess.run([executable, *flags, "-S", str(script)],
                                capture_output=True, text=True, timeout=30, cwd=ROOT)
        if result.returncode or not result_path.exists():
            raise AssertionError(f"{name} project checking failed: {result.stdout}\n{result.stderr}")
        report = json.loads(result_path.read_text())
        report["expected_column"] = len(bad_source.splitlines()[3].split("missing")[0].encode()) + 1
        report["dependency"] = str(dependency.resolve())
        assert entry.read_bytes() == entry_source.replace("\n", line_ending).encode()
        assert dependency.read_bytes() == valid_source.replace("\n", line_ending).encode()
        return report


def inspect_formatting(name, executable, ending, final_newline):
    import shlex
    with tempfile.TemporaryDirectory(prefix="format buffer 'quoted' ") as directory:
        directory = Path(directory)
        path = directory / "Buffer.fib"
        original = ['main:String', 'main="saved"']
        raw = ending.join(original) + (ending if final_newline else "")
        path.write_bytes(raw.encode())
        edited = ['main:String', 'main=appendString"🌍  e\u0301""!"  -- keep  text  ']
        formatted = ['main : String', 'main = appendString "🌍  e\u0301" "!"  -- keep  text  ']
        snapshot = ending.join(edited) + (ending if final_newline else "")
        fake = directory / "fake formatter"
        fake.write_text("#!/bin/sh\nexit 1\n")
        fake.chmod(0o755)
        temp_log = directory / "temporary.txt"
        report_path = directory / "report.json"
        commands = [
            "set nocompatible", "set encoding=utf-8", "set nomore", "set hidden",
            f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})",
            "filetype plugin on",
            f"let g:fibril_executable = {vim_literal(ROOT / 'build/exec/fibril')}",
            f"execute 'edit ' . fnameescape({vim_literal(path)})",
            "setlocal undolevels=321",
            f"call setline(2, {vim_literal(edited[1])})",
            "let report = {}", "let source_buffer = bufnr('%')",
            "let source_window = win_getid()", "let saved_options = [&ff, &eol, &fenc, &bomb]",
            "let undo_options = [&g:undolevels, &l:undolevels]",
            "call cursor(2, 20)",
            "let report.handled = fibril#format()", "let report.formatted = getline(1, '$')",
            "let report.modified = &modified",
            "let report.same_context = bufnr('%') == source_buffer && win_getid() == source_window",
            "let report.options = [&ff, &eol, &fenc, &bomb] == saved_options",
            "let report.undo_options = [&g:undolevels, &l:undolevels] == undo_options",
            "undo", "let report.undone = getline(1, '$')", "let report.undo_modified = &modified",
            "redo", "let before_tick = b:changedtick", "let before_undo = changenr()",
            "FibrilFormat",
            "let report.noop = b:changedtick == before_tick && changenr() == before_undo",
            "let long_source = ['module Main', 'import Data.Package', 'import Data.Message', '', 'main : IO Unit', 'main = putStrLn (Data.Message.render (Data.Message.MkMessage True (Data.Package.recover (Data.Package.MkPackage String \"Records\"))))']",
            "call setline(1, long_source)",
            "let report.wrap_handled = fibril#format()",
            "let report.wrapped = getline(1, '$')",
            "undo", "let report.wrap_undo = getline(1, '$') == long_source",
            "redo", "let before_tick = b:changedtick", "let before_undo = changenr()",
            "let report.wrap_noop_handled = fibril#format()",
            "let report.wrap_noop = b:changedtick == before_tick && changenr() == before_undo",
            "edit!",
            f"call setline(1, [{', '.join(vim_literal(line) for line in formatted)}])",
            "let previous_lines = getline(1, '$')", "let previous_undo = changenr()",
            f"let g:fibril_executable = {vim_literal(fake)}",
            "let report.faults = []",
        ]
        canonical = ending.join(formatted) + (ending if final_newline else "")
        envelope = {"version": 1, "coordinates": "unicode-scalars;offset=0;line=1;column=1",
                    "original": canonical, "formatted": canonical}
        faults = [
            ({**envelope, "version": 2}, 0),
            ({**envelope, "original": snapshot}, 0),
            ({**envelope, "formatted": "replacement"}, 0),
            ({**envelope, "formatted": canonical + "\n"}, 0),
            ({**envelope, "formatted": False}, 0),
            (envelope, 1),
        ]
        if ending == "\r\n":
            faults.append(({**envelope, "formatted": canonical.replace("\r\n", "\n")}, 0))
        else:
            faults.append(({**envelope, "formatted": canonical.replace("\n", "\r\n")}, 0))
        for payload, status in faults:
            shell = ["#!/bin/sh", 'printf \'%s\' "$3" > ' + shlex.quote(str(temp_log)),
                     "printf '%s\\n' " + shlex.quote(json.dumps(payload)), f"exit {status}"]
            commands += [
                f"call writefile([{', '.join(vim_literal(x) for x in shell)}], {vim_literal(fake)})",
                "let handled = fibril#format()",
                "let temporary = join(readfile(" + vim_literal(temp_log) + "), '')",
                "call add(report.faults, handled == 0 && getline(1, '$') == previous_lines && changenr() == previous_undo && !filereadable(temporary))",
            ]
        commands += [
            f"let g:fibril_executable = {vim_literal(ROOT / 'build/exec/fibril')}",
            "setlocal readonly", "let report.readonly = fibril#format()", "setlocal noreadonly",
            "call setline(2, 'main =')", "let invalid_lines = getline(1, '$')",
            "let report.syntax_failure = fibril#format()",
            "let report.syntax_preserved = getline(1, '$') == invalid_lines",
            "let report.plug = !empty(maparg('<Plug>(FibrilFormat)', 'n'))",
            "execute b:undo_ftplugin",
            "let report.undo_command = exists(':FibrilFormat')",
            "let report.undo_plug = maparg('<Plug>(FibrilFormat)', 'n')",
            "enew!", "setfiletype fibril",
            f"call setline(1, {vim_literal('appendString\"new\"\"buffer\"')})",
            "let report.unnamed = fibril#format()",
            "let report.unnamed_text = getline(1)",
            "let report.unnamed_name = expand('%:p')",
            "let report.messages = execute('messages')",
            f"call writefile([json_encode(report)], {vim_literal(report_path)})", "qa!",
        ]
        script = directory / "format.vim"
        script.write_text("\n".join(commands) + "\n")
        flags = ["--headless", "-u", "NONE", "-i", "NONE", "-n"] if name == "nvim" else [
            "-Nu", "NONE", "-i", "NONE", "-n", "-es"]
        result = subprocess.run([executable, *flags, "-S", str(script)], capture_output=True,
                                text=True, timeout=30, cwd=ROOT)
        if result.returncode or not report_path.exists():
            raise AssertionError(f"{name} formatting failed: {result.stdout}\n{result.stderr}")
        assert path.read_bytes() == raw.encode(), "formatter wrote the original source file"
        data = json.loads(report_path.read_text())
        data["expected"] = formatted
        data["edited"] = edited
        return data


class EditorTests(unittest.TestCase):
    def test_package_definition_in_installed_editors(self):
        import shlex
        binary = ROOT / 'build/exec/fibril'
        if not binary.exists():
            self.skipTest('build Fibril first')
        for name, executable in EDITORS:
            for application in (False, True):
                with self.subTest(editor=name, application=application), tempfile.TemporaryDirectory(prefix='fibril package editor ') as directory:
                    root = Path(directory)
                    a, b = root / 'a', root / 'b'
                    (a / 'src/A').mkdir(parents=True)
                    (b / 'src/B').mkdir(parents=True)
                    (a / 'fibril.yaml').write_text('schema: 1\nname: a\nmodule-prefix: A\nsource-dir: src\nfoundation: de-morgan\nmodules: [A.Value]\ndependencies: {}\n')
                    manifest = b / 'fibril.yaml'
                    manifest.write_text('schema: 1\nname: b\nmodule-prefix: B\nsource-dir: src\nfoundation: de-morgan\n' + ('entry: Main\n' if application else '') + 'modules: [B.Facade]\ndependencies:\n  a:\n    path: ../a\n')
                    target = a / 'src/A/Value.fib'
                    target.write_text('module A.Value\nexport\nx : String\nx = "ok"\n')
                    facade = b / 'src/B/Facade.fib'
                    facade.write_text('module B.Facade\nimport A.Value (x)\nexport\ny : String\ny = x\n')
                    source = b / 'src/Main.fib' if application else facade
                    if application:
                        source.write_text('module Main\nimport A.Value\nmain : IO Unit\nmain = putStrLn A.Value.x\n')
                    row, column = (4, 25) if application else (5, 5)
                    result = subprocess.run([str(binary), 'definition', '--package', str(manifest), str(row), str(column), str(source)], capture_output=True, text=True, timeout=120)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    forged = json.loads(result.stdout)
                    sibling_packet = json.loads(result.stdout)
                    sibling = a / 'sibling'
                    sibling.mkdir()
                    sibling_target = sibling / 'Value.fib'
                    sibling_target.write_text(target.read_text())
                    for item in sibling_packet['package_scope']['inventory']:
                        if item['name'] == 'a':
                            item['source_root'] = str(sibling.resolve())
                    for item in sibling_packet['sources']:
                        if item['path'] == str(target.resolve()):
                            item['path'] = str(sibling_target.resolve())
                    sibling_packet['definition']['path'] = str(sibling_target.resolve())
                    bad_sibling = root / 'bad-sibling-compiler'
                    bad_sibling.write_text('#!/bin/sh\nprintf "%s\\n" ' + shlex.quote(json.dumps(sibling_packet)) + '\n')
                    bad_sibling.chmod(0o755)
                    forged_directory = json.loads(json.dumps(sibling_packet))
                    for item in forged_directory['manifests']:
                        if item['name'] == 'a':
                            item['source_dir'] = 'sibling'
                    bad_directory = root / 'bad-directory-compiler'
                    bad_directory.write_text('#!/bin/sh\nif [ "$1" = manifest ]; then exec ' + shlex.quote(str(binary)) + ' "$@"; fi\nprintf "%s\\n" ' + shlex.quote(json.dumps(forged_directory)) + '\n')
                    bad_directory.chmod(0o755)
                    outside = root / 'outside'
                    outside.mkdir()
                    forged_target = outside / 'Value.fib'
                    forged_target.write_text(target.read_text())
                    for item in forged['package_scope']['inventory']:
                        if item['name'] == 'a':
                            item['source_root'] = str(outside.resolve())
                    for item in forged['sources']:
                        if item['path'] == str(target.resolve()):
                            item['path'] = str(forged_target.resolve())
                    forged['definition']['path'] = str(forged_target.resolve())
                    bad = root / 'bad-compiler'
                    bad.write_text('#!/bin/sh\nprintf "%s\\n" ' + shlex.quote(json.dumps(forged)) + '\n')
                    bad.chmod(0o755)
                    fake = root / 'fake-compiler'
                    fake.write_text('#!/bin/sh\n' + shlex.quote(str(binary)) + ' "$@"\nstatus=$?\nprintf " " >> ' + shlex.quote(str(a / 'fibril.yaml')) + '\nexit "$status"\n')
                    fake.chmod(0o755)
                    report_path = root / 'result.json'
                    commands = [
                        'set nocompatible', 'set encoding=utf-8', 'set nomore', 'set hidden',
                        f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})", 'filetype plugin on',
                        f'let g:fibril_executable = {vim_literal(binary)}',
                        f'let g:fibril_package_manifest = {vim_literal(manifest)}',
                        f"execute 'edit ' . fnameescape({vim_literal(source)})", 'let source_buffer = bufnr(\'%\')',
                        f'call cursor({row}, {column})', 'let report = {}',
                        'let report.handled = fibril#definition_package(g:fibril_package_manifest)',
                        f"let report.target = resolve(expand('%:p')) ==# resolve({vim_literal(target)}) && line('.') == 4 && col('.') == 1",
                        "let target_buffer = bufnr('%')", 'execute "buffer " . source_buffer',
                        "call setbufline(target_buffer, 4, getbufline(target_buffer, 4)[0] . ' ')",
                        f'call cursor({row}, {column})',
                        'let report.modified_target = fibril#definition_package(g:fibril_package_manifest)',
                        'execute "buffer! " . target_buffer', 'edit!', 'execute "buffer " . source_buffer',
                        f"execute 'edit ' . fnameescape({vim_literal(a / 'fibril.yaml')})", 'let manifest_buffer = bufnr(\'%\')',
                        "call setline(1, getline(1) . ' ')", 'execute "buffer " . source_buffer',
                        f'call cursor({row}, {column})',
                        'let report.modified_manifest = fibril#definition_package(g:fibril_package_manifest)',
                        'execute "buffer! " . manifest_buffer', 'edit!', 'execute "buffer " . source_buffer',
                        f'let g:fibril_executable = {vim_literal(bad)}', f'call cursor({row}, {column})',
                        'let report.bad_root = fibril#definition_package(g:fibril_package_manifest)',
                        f'let g:fibril_executable = {vim_literal(bad_sibling)}', f'call cursor({row}, {column})',
                        'let report.bad_sibling = fibril#definition_package(g:fibril_package_manifest)',
                        f'let g:fibril_executable = {vim_literal(bad_directory)}', f'call cursor({row}, {column})',
                        'let report.bad_directory = fibril#definition_package(g:fibril_package_manifest)',
                        f'let g:fibril_executable = {vim_literal(fake)}', f'call cursor({row}, {column})',
                        'let report.changed_manifest = fibril#definition_package(g:fibril_package_manifest)',
                        "let report.preserved = resolve(expand('%:p')) ==# resolve(" + vim_literal(source) + ')',
                        "let report.plug = !empty(maparg('<Plug>(FibrilDefinitionPackage)', 'n'))",
                        "let report.messages = execute('messages')", 'execute b:undo_ftplugin',
                        "let report.undo_command = exists(':FibrilDefinitionPackage')",
                        "let report.undo_plug = maparg('<Plug>(FibrilDefinitionPackage)', 'n')",
                        f'call writefile([json_encode(report)], {vim_literal(report_path)})', 'qa!',
                    ]
                    script = root / 'test.vim'
                    script.write_text('\n'.join(commands) + '\n')
                    flags = ['--headless', '-u', 'NONE', '-i', 'NONE', '-n'] if name == 'nvim' else ['-Nu', 'NONE', '-i', 'NONE', '-n', '-es']
                    result = subprocess.run([executable, *flags, '-S', str(script)], capture_output=True, text=True, timeout=120, cwd=ROOT)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    report = json.loads(report_path.read_text())
                    self.assertEqual(report['handled'], 1, report['messages'])
                    self.assertTrue(report['target'], report['messages'])
                    self.assertEqual(report['modified_target'], 0, report['messages'])
                    self.assertEqual(report['modified_manifest'], 0, report['messages'])
                    self.assertEqual(report['changed_manifest'], 0, report['messages'])
                    self.assertEqual(report['bad_root'], 0, report['messages'])
                    self.assertEqual(report['bad_sibling'], 0, report['messages'])
                    self.assertEqual(report['bad_directory'], 0, report['messages'])
                    self.assertIn('outside its manifest directory', report['messages'])
                    self.assertIn('no longer resolves to its checked root', report['messages'])
                    self.assertIn('manifest inspection disagrees', report['messages'])
                    self.assertTrue(report['preserved'], report['messages'])
                    self.assertTrue(report['plug'])
                    self.assertEqual(report['undo_command'], 0)
                    self.assertEqual(report['undo_plug'], '')

    def test_package_definition_rejects_retargeted_paths(self):
        import shlex
        binary = ROOT / 'build/exec/fibril'
        if not binary.exists():
            self.skipTest('build Fibril first')
        for name, executable in EDITORS:
            for mode in ('source', 'dependency', 'module', 'intermediate', 'hook-source', 'hook-dependency', 'hook-module', 'hook-intermediate'):
                with self.subTest(editor=name, mode=mode), tempfile.TemporaryDirectory(prefix='fibril package symlink ') as directory:
                    root = Path(directory)
                    a, b = root / 'a', root / 'b'
                    (b / 'src/B').mkdir(parents=True)
                    (a / 'old/A').mkdir(parents=True)
                    (a / 'new/A').mkdir(parents=True)
                    value = 'module A.Value\nexport\nx : String\nx = "ok"\n'
                    kind = mode.removeprefix('hook-')
                    if kind == 'module':
                        (a / 'old/A/old.fib').write_text(value)
                        (a / 'old/A/new.fib').write_text(value)
                        (a / 'old/A/Value.fib').symlink_to('old.fib')
                    else:
                        (a / 'old/A/Value.fib').write_text(value)
                    (a / 'new/A/Value.fib').write_text(value)
                    if kind == 'intermediate':
                        (a / 'old/A').rename(a / 'old/inside')
                        (a / 'old/A').symlink_to('inside', target_is_directory=True)
                        escaped = root / 'escaped'
                        escaped.mkdir()
                        (escaped / 'Value.fib').symlink_to(a / 'old/inside/Value.fib')
                    (a / 'fibril.yaml').write_text('schema: 1\nname: a\nmodule-prefix: A\nsource-dir: src\nfoundation: de-morgan\nmodules: [A.Value]\ndependencies: {}\n')
                    (a / 'src').symlink_to('old', target_is_directory=True)
                    (root / 'link-a').symlink_to('a', target_is_directory=True)
                    other = root / 'a2'
                    shutil.copytree(a, other, symlinks=True)
                    manifest = b / 'fibril.yaml'
                    manifest.write_text('schema: 1\nname: b\nmodule-prefix: B\nsource-dir: src\nfoundation: de-morgan\nmodules: [B.Facade]\ndependencies:\n  a:\n    path: ../link-a\n')
                    source = b / 'src/B/Facade.fib'
                    source.write_text('module B.Facade\nimport A.Value (x)\nexport\ny : String\ny = x\n')
                    link = (a / 'src') if kind == 'source' else ((a / 'old/A/Value.fib') if kind == 'module' else ((a / 'old/A') if kind == 'intermediate' else (root / 'link-a')))
                    replacement = 'new' if kind == 'source' else ('new.fib' if kind == 'module' else (str(escaped) if kind == 'intermediate' else 'a2'))
                    fake = root / 'retarget-compiler'
                    fake.write_text('#!/bin/sh\n' + shlex.quote(str(binary)) + ' "$@"\nstatus=$?\nln -sfn ' + shlex.quote(replacement) + ' ' + shlex.quote(str(link)) + '\nexit "$status"\n')
                    fake.chmod(0o755)
                    report_path = root / 'result.json'
                    commands = ['set nocompatible', 'set encoding=utf-8', 'set nomore', 'set hidden',
                        f"execute 'set runtimepath^=' . fnameescape({vim_literal(RUNTIME)})", 'filetype plugin on',
                        f'let g:fibril_executable = {vim_literal(fake)}',
                        f'let g:fibril_package_manifest = {vim_literal(manifest)}',
                        f"execute 'edit ' . fnameescape({vim_literal(source)})", 'call cursor(5, 5)',
                        'let report = {}', 'let report.handled = fibril#definition_package(g:fibril_package_manifest)',
                        "let report.preserved = resolve(expand('%:p')) ==# resolve(" + vim_literal(source) + ')',
                        "let report.messages = execute('messages')",
                        f'call writefile([json_encode(report)], {vim_literal(report_path)})', 'qa!']
                    if mode.startswith('hook-'):
                        commands[commands.index(f'let g:fibril_executable = {vim_literal(fake)}')] = f'let g:fibril_executable = {vim_literal(binary)}'
                        hook = 'ln -sfn ' + shlex.quote(replacement) + ' ' + shlex.quote(str(link))
                        position = commands.index('call cursor(5, 5)')
                        pattern = '*/A/old.fib' if kind == 'module' else ('*/inside/Value.fib' if kind == 'intermediate' else '*/A/Value.fib')
                        commands[position:position] = [f'let g:retarget_command = {vim_literal(hook)}',
                            'augroup FibrilTestRetarget', 'autocmd!',
                            'autocmd BufReadPost ' + pattern + ' call system(g:retarget_command)', 'augroup END']
                    script = root / 'test.vim'
                    script.write_text('\n'.join(commands) + '\n')
                    flags = ['--headless', '-u', 'NONE', '-i', 'NONE', '-n'] if name == 'nvim' else ['-Nu', 'NONE', '-i', 'NONE', '-n', '-es']
                    result = subprocess.run([executable, *flags, '-S', str(script)], capture_output=True, text=True, timeout=120, cwd=ROOT)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    report = json.loads(report_path.read_text())
                    self.assertEqual(report['handled'], 0, report['messages'])
                    if not mode.startswith('hook-'):
                        self.assertTrue(report['preserved'], report['messages'])
                    self.assertIn('no longer resolves', report['messages'])

    def test_formatting_in_installed_editors(self):
        if not (ROOT / "build/exec/fibril").exists():
            self.skipTest("build Fibril first")
        for name, executable in EDITORS:
            for ending in ("\n", "\r\n"):
                for final_newline in (False, True):
                    with self.subTest(editor=name, ending=ending, final_newline=final_newline):
                        report = inspect_formatting(name, executable, ending, final_newline)
                        self.assertEqual(report["handled"], 1, report["messages"])
                        self.assertEqual(report["formatted"], report["expected"])
                        self.assertTrue(report["modified"])
                        self.assertTrue(report["same_context"])
                        self.assertTrue(report["options"])
                        self.assertTrue(report["undo_options"])
                        self.assertEqual(report["undone"], report["edited"])
                        self.assertTrue(report["undo_modified"])
                        self.assertTrue(report["noop"])
                        self.assertEqual(report["wrap_handled"], 1, report["messages"])
                        self.assertEqual(report["wrapped"][-5:], [
                            "main = putStrLn", "  (Data.Message.render",
                            "    (Data.Message.MkMessage True", "      (Data.Package.recover",
                            '        (Data.Package.MkPackage String "Records"))))'])
                        self.assertTrue(report["wrap_undo"])
                        self.assertTrue(report["wrap_noop"])
                        self.assertTrue(all(report["faults"]), report["messages"])
                        self.assertEqual(report["readonly"], 0)
                        self.assertEqual(report["syntax_failure"], 0)
                        self.assertTrue(report["syntax_preserved"])
                        self.assertTrue(report["plug"])
                        self.assertEqual(report["undo_command"], 0)
                        self.assertEqual(report["undo_plug"], "")
                        self.assertEqual(report["unnamed"], 1, report["messages"])
                        self.assertEqual(report["unnamed_text"], 'appendString "new" "buffer"')
                        self.assertEqual(report["unnamed_name"], "")

    def test_project_checking_in_installed_editors(self):
        if not (ROOT / "build/exec/fibril").exists():
            self.skipTest("build Fibril first")
        for name, executable in EDITORS:
            for ending in ("\n", "\r\n"):
                with self.subTest(editor=name, line_ending=ending):
                    report = inspect_project_checking(name, executable, ending)
                    self.assertEqual(report["unloaded"], 1)
                    self.assertTrue(report["not_loaded"])
                    self.assertEqual(report["unloaded_item"]["valid"], 0)
                    self.assertEqual(report["unloaded_item"]["lnum"], 0)
                    self.assertIn("open source", report["unloaded_item"]["text"])
                    self.assertIn(report["dependency"], report["unloaded_item"]["text"])
                    self.assertEqual(report["loaded_item"]["valid"], 1)
                    self.assertEqual(report["loaded_item"]["lnum"], 4)
                    self.assertEqual(report["loaded_item"]["col"], report["expected_column"])
                    self.assertTrue(report["correct_buffer"])
                    self.assertTrue(report["jumped"])
                    self.assertTrue(report["unchanged"])
                    self.assertEqual(report["modified"], 0)
                    self.assertTrue(report["preserved"])
                    self.assertTrue(all(report["faults"]), report["messages"])
                    self.assertEqual(report["stale"], 0)
                    self.assertTrue(report["stale_preserved"])
                    self.assertEqual(report["unavailable"], 1)
                    self.assertEqual(report["unavailable_item"]["valid"], 0)
                    self.assertEqual(report["unavailable_item"]["lnum"], 0)
                    self.assertIn("byte offset 4", report["unavailable_item"]["text"])
                    self.assertEqual(report["accepted"], 1, report["messages"])
                    self.assertEqual(report["accepted_items"], [])
                    self.assertTrue(report["no_extra_window"])
                    self.assertTrue(report["plug"])
                    self.assertEqual(report["builtin_help"], 1, report["messages"])
                    self.assertTrue(report["builtin_buffer"])
                    self.assertEqual(report["prelude_help"], 1, report["messages"])
                    self.assertTrue(report["prelude_buffer"])
                    self.assertEqual(report["definition_unloaded"], 1, report["messages"])
                    self.assertTrue(report["definition_auto"], report["messages"])
                    self.assertEqual(report["definition_modified"], 0)
                    self.assertTrue(report["definition_jump"], report["messages"])
                    self.assertTrue(report["library_definition"], report["messages"])
                    self.assertEqual(report["read_hook_refused"], 0)
                    self.assertTrue(report["read_hook_preserved"], report["messages"])
                    self.assertTrue(report["definition_plug"])
                    self.assertTrue(all(report["definition_faults"]), report["messages"])
                    self.assertEqual(report["definition_undo_command"], 0)
                    self.assertEqual(report["definition_undo_plug"], "")
                    self.assertEqual(report["undo_command"], 0)
                    self.assertEqual(report["undo_plug"], "")
                    self.assertNotIn("must not execute", report["messages"])

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
