#!/usr/bin/env python3
"""Smoke-test the built CLI independently of its pure implementation helpers."""
from pathlib import Path
import subprocess
import tempfile
import random
import unittest
import json

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / "build/exec/fibril"


def run(*args):
    return subprocess.run([str(EXE), *args], cwd=ROOT, text=True,
                          capture_output=True, timeout=20)


class CLITests(unittest.TestCase):
    def test_help(self):
        result = run("--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("fibril demo", result.stdout)
        self.assertIn("not implemented yet", result.stdout)

    def test_version(self):
        result = run("--version")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Fibril 0.1.0-dev", result.stdout)

    def test_demo(self):
        result = run("demo")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for expected in ("Identity type: (Pi 0 Type0 (Pi 1 v0 v1))",
                         "Erased checking: accepted", "closed usage []",
                         "Linear duplication: rejected", "De Morgan interval law: passed",
                         "disjoint, not exhaustive", "not a soundness proof"):
            self.assertIn(expected, result.stdout)

    def test_source_loader_accepts_valid_unicode_and_empty_files(self):
        for text in ("", "identity x = x", "λ x → x\r\n", "日本語 🌊", "\ufffd"):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.fib"
                path.write_bytes(text.encode("utf-8"))
                result = run("validate-source", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("not type checked", result.stdout)

    def test_source_loader_rejects_bad_bytes_and_controls(self):
        for data, expected in ((b"\xff", "byte 0"),
                               (b"A\xe2\x82A", "byte 3"),
                               (b"\xed\xa0\x80", "surrogate"),
                               (b"\xf4\x90\x80\x80", "U+10FFFF"),
                               (b"x\x00", "control"),
                               ("x\u202e".encode("utf-8"), "bidirectional"),
                               (b"\xef\xbb\xbf", "marks")):
            with self.subTest(data=data), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "source.fib"
                path.write_bytes(data)
                result = run("validate-source", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected, result.stdout)

    def test_source_loader_limits_and_missing_file(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.fib"
            path.write_bytes(b"a" * 65536)
            self.assertEqual(run("validate-source", str(path)).returncode, 0)
            path.write_bytes(b"a" * 65537)
            result = run("validate-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("limit", result.stdout)
            path.unlink()
            self.assertNotEqual(run("validate-source", str(path)).returncode, 0)

    def test_malformed_bytes_agree_with_python_strict_rejection(self):
        rng = random.Random(3629)
        malformed = []
        while len(malformed) < 30:
            data = bytes(rng.randrange(256) for _ in range(rng.randint(1, 6)))
            try:
                data.decode("utf-8", errors="strict")
            except UnicodeDecodeError:
                malformed.append(data)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.fib"
            for data in malformed:
                with self.subTest(data=data):
                    path.write_bytes(data)
                    result = run("validate-source", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("UTF-8", result.stdout)

    def test_lexer_command_reports_tokens_and_rejects_unsupported_text(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expression.fib"
            path.write_text("λ x ⇒ x", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("1:1-1:2 lambda", result.stdout)
            self.assertIn("1:5-1:6 =>", result.stdout)
            path.write_text("x @ y", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("1:3", result.stdout)

    def test_source_check_command(self):
        result = run("check", "examples/core/identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertIn("(Pi 0 Type0 (Pi 1 v0 v1))", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expression.fib"
            path.write_text("Type 0", encoding="utf-8")
            self.assertNotEqual(run("check", str(path)).returncode, 0)
            result = run("check", "--erased", str(path))
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("no runtime-use guarantee", result.stdout)
            self.assertIn("Type: Type1", result.stdout)
            path.write_text("missing", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:1:1: Resolution:", result.stdout)
            self.assertIn("  1 | missing", result.stdout)
            self.assertIn("^", result.stdout)
            path.write_text("Type", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Parsing:", result.stdout)

    def test_ordinary_io_functions_and_portable_prelude(self):
        result = run("run", "examples/core/io-functions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "This is a Fibril library function.\n")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "shadow.fib"
            path.write_text(
                "putStrLn : Bool -> IO Unit\n"
                "putStrLn = \\(flag : Bool) => pure Unit ()\n"
                "main : IO Unit\nmain = putStrLn True\n", encoding="utf-8")
            result = subprocess.run([str(EXE), "run", str(path)], cwd=directory,
                                    text=True, capture_output=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "")
            path.write_text(
                "emit : (1 text : String) -> IO Unit\n"
                "emit = \\(1 text : String) => do\n"
                "  putStrLn text\n  putStrLn text\n"
                "main : IO Unit\nmain = emit \"linear\"\n", encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Binder usage", result.stderr)

    def test_console_pure_arguments(self):
        result = run("run", "examples/core/console-expressions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello from a pure function!\nString computation works.\nLocal bindings work too.\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/console-expressions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertNotIn("Hello from a pure function!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "arguments.fib"
            start = 'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
            for expression in ('True', 'missing', r'((\(1 x : String) => "discard") "input")',
                               r'((\(0 x : String) => x) "input")'):
                with self.subTest(expression=expression):
                    path.write_text(start + "  putStrLn " + expression + "\n", encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.write_text(start + "  putStrLn missing\n", encoding="utf-8")
            result = run("run", str(path))
            self.assertIn(f"{path}:4:12: Resolution:", result.stderr)
            self.assertIn("^", result.stderr)
            path.write_text(start + "  putStrLn True\n", encoding="utf-8")
            result = run("run", str(path))
            self.assertIn("inferred: Bool; expected: String", result.stderr)
            self.assertNotIn("^", result.stderr)

    def test_pure_string_program(self):
        result = run("check", "examples/core/string-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: String", result.stdout)
        result = run("eval", "examples/core/string-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: "Hello from pure Fibril."', result.stdout)
        result = run("run", "examples/core/string-identity.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("use eval", result.stderr)

    def test_structured_lambda_case_and_signature_layout(self):
        # Exact partially formatted report: don't skip an already-multiline RHS.
        source = (
            'module Patterns\nimport Data.Package\nimport Data.Message\n\n'
            '0 payloadType : (0 package : Data.Package.Package) -> Type 0\n'
            'payloadType = \\(0 package : Data.Package.Package) => case package return (\\(0 self : Data.Package.Package) => Type 0) of (0 Item : Type 0) (1 value : Item) => Item\n\n'
            'recover : (1 package : Data.Package.Package) -> payloadType package\n'
            'recover = \\(1 package : Data.Package.Package) => case package return (\\(0 self : Data.Package.Package) => payloadType self) of (0 Item : Type 0) (1 value : Item) => value\n\n'
            'main : IO Unit\nmain = putStrLn\n  (case Data.Message.MkMessage True\n'
            '    (recover\n      (Data.Package.MkPackage String "Patterns")) return (\\(0 self : Data.Message.Message) => String) of (1 enabled : Bool) (1 text : String) => if enabled then appendString text "!" else text)\n')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Patterns.fib"
            for ending in ("\n", "\r\n"):
                path.write_bytes(source.replace("\n", ending).encode())
                result = run("format", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('payloadType = \\(0 package : Data.Package.Package) =>\n  case package\n', result.stdout)
                self.assertIn('    of (0 Item : Type 0) (1 value : Item) =>\n      Item', result.stdout)
                self.assertIn('    of (1 enabled : Bool) (1 text : String) =>\n      if enabled', result.stdout)
                self.assertLessEqual(max(map(len, result.stdout.splitlines())), 100)
                path.write_bytes(result.stdout.replace("\n", ending).encode())
                again = run("format", str(path))
                self.assertEqual(again.stdout, result.stdout)
            # Signatures and long conditional branches, not only application groups.
            path.write_text(
                'combine : (0 Element : Type 0) -> (combine : (left : Element) -> (right : Element) -> Element) -> (left : Element) -> (middle : Element) -> (right : Element) -> Element\n'
                'combine = \\(0 Element : Type 0) => \\(combine : (left : Element) -> (right : Element) -> Element) => \\(left : Element) => \\(middle : Element) => \\(right : Element) => combine (combine left middle) right\n'
                'main : Bool\nmain = True\n')
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('->\n', result.stdout)
            self.assertIn('=>\n', result.stdout)
            path.write_text(result.stdout)
            self.assertEqual(run("format", str(path)).stdout, result.stdout)
            self.assertEqual(run("check", str(path)).returncode, 0)
            path.write_text(
                'main : String\nmain = if equalString "' + "a" * 40 + '" "' + "b" * 40 +
                '" then appendString "long branch" " value" else appendString "other branch" " value"\n')
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("\n  then ", result.stdout)
            self.assertIn("\n  else ", result.stdout)
            path.write_text(result.stdout)
            self.assertEqual(run("format", str(path)).stdout, result.stdout)
            self.assertEqual(run("check", str(path)).returncode, 0)
            # Verify the real dependency graph after applying the reported layout.
            for file in (ROOT / "examples/modules/records/Data").glob("*.fib"):
                destination = root / "Data" / file.name
                destination.parent.mkdir(exist_ok=True)
                destination.write_bytes(file.read_bytes())
            path.write_text(source)
            result = run("format", str(path))
            path.write_text(result.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Patterns!\n")

    def test_parenthesized_application_wrapping(self):
        source = ('module Main\nimport Data.Package\nimport Data.Message\n\nmain : IO Unit\n'
                  'main = putStrLn (Data.Message.render (Data.Message.MkMessage True (Data.Package.recover (Data.Package.MkPackage String "Records"))))\n')
        expected = ('module Main\nimport Data.Package\nimport Data.Message\n\nmain : IO Unit\n'
                    'main = putStrLn\n  (Data.Message.render\n    (Data.Message.MkMessage True\n'
                    '      (Data.Package.recover\n        (Data.Package.MkPackage String "Records"))))\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Main.fib"
            for ending in ("\n", "\r\n"):
                for final in (False, True):
                    data = source.replace("\n", ending)
                    formatted = expected.replace("\n", ending)
                    if not final:
                        data = data[:-len(ending)]
                        formatted = formatted[:-len(ending)]
                    path.write_bytes(data.encode())
                    result = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                    self.assertEqual(result.returncode, 0, result.stderr.decode())
                    self.assertEqual(result.stdout, formatted.encode())
                    self.assertEqual(path.read_bytes(), data.encode())
                    path.write_bytes(result.stdout)
                    again = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                    self.assertEqual(again.stdout, result.stdout)
            # Flat do actions must not accidentally become multiline statements.
            do_source = 'main : IO Unit\nmain = do\n  putStrLn (appendString "' + "a" * 110 + '" "b")\n'
            path.write_text(do_source)
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, do_source)
            literal = 'putStrLn "' + "x" * 140 + '"'
            path.write_text(literal)
            self.assertEqual(run("format", str(path)).stdout, literal)
            # Reformat a genuine project, then check/run the changed layout.
            original = ROOT / "examples/modules/records"
            for file in original.rglob("*.fib"):
                destination = Path(directory) / file.relative_to(original)
                destination.parent.mkdir(parents=True, exist_ok=True)
                text = subprocess.run([str(EXE), "format", str(file)], capture_output=True)
                self.assertEqual(text.returncode, 0, text.stderr.decode())
                destination.write_bytes(text.stdout)
            result = run("run", "--source-dir", directory, str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Records!\n")

    def test_conservative_source_formatting(self):
        with tempfile.TemporaryDirectory(prefix="format 'quoted' ") as directory:
            path = Path(directory) / "Main.fib"
            for ending in ("\n", "\r\n"):
                source = ('-- comment  spacing\t stays  \n'
                          'main:IO  Unit\nmain=putStrLn(appendString"🌍  e\u0301""!")  -- trailing  text  \n')
                expected = ('-- comment  spacing\t stays  \n'
                            'main : IO Unit\nmain = putStrLn (appendString "🌍  e\u0301" "!")  -- trailing  text  \n')
                original = source.replace("\n", ending).encode()
                path.write_bytes(original)
                result = run("format", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                # subprocess text mode normalizes CRLF, so inspect actual output bytes.
                raw = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                self.assertEqual(raw.stdout, expected.replace("\n", ending).encode())
                self.assertEqual(path.read_bytes(), original)
                report = json.loads(run("format", "--json", str(path)).stdout)
                self.assertEqual(report["original"].encode(), original)
                self.assertEqual(report["formatted"].encode(), raw.stdout)
                self.assertEqual(run("format", "--check", str(path)).returncode, 1)
                path.write_bytes(raw.stdout)
                canonical = path.read_bytes()
                again = subprocess.run([str(EXE), "format", str(path)], capture_output=True)
                self.assertEqual(again.stdout, canonical)
                result = run("format", "--check", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "")
                self.assertEqual(result.stderr, "")
            for source in ("", "-- only comment  ", "True", 'main : IO Unit\nmain = do\n\tputStrLn  "x"\n\tputStrLn "y"\n'):
                path.write_text(source)
                result = run("format", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                if source in ("", "-- only comment  ", "True"):
                    self.assertEqual(result.stdout, source)
                else:
                    self.assertIn('\n\tputStrLn "x"\n\tputStrLn "y"\n', result.stdout)
            # Formatting is syntax-only, not elaboration admission or checking.
            path.write_text('module Main\nrecord R:Type 0 where\n  constructor MkR\n'
                            '  eliminator useR\n  1 x:Bool\n  1 y:Bool\n  projection getX x\n'
                            'main:Bool\nmain="wrong"\n')
            result = run("format", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("record R : Type 0 where", result.stdout)
            for content in (b"\xff", b"\xef\xbb\xbfTrue", b"main :", b"\x00"):
                path.write_bytes(content)
                result = run("format", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertEqual(path.read_bytes(), content)
            # Insertion of canonical spaces cannot evade the output cap.
            prefix = 'main:String\nmain="'
            content = prefix + "a" * (65536 - len(prefix) - 2) + '"\n'
            path.write_text(content)
            result = run("format", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("65536", result.stderr)

    def test_formatter_corpus_idempotence(self):
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in sorted((ROOT / "examples/core").glob("*.fib")):
                result = run("format", str(path))
                # Every current core fixture should remain syntactically inspectable.
                self.assertEqual(result.returncode, 0, str(path) + result.stderr)
                formatted = target / path.name
                formatted.write_text(result.stdout)
                again = run("format", str(formatted))
                self.assertEqual(again.returncode, 0, again.stderr)
                self.assertEqual(again.stdout, result.stdout, str(path))
                self.assertEqual(run("check", str(path)).returncode,
                                 run("check", str(formatted)).returncode, str(path))

    def test_explicit_declaration_elaboration(self):
        result = run("elaborate", "examples/modules/record-projections/Data/Dictionary.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertFalse(report["checked"])
        self.assertEqual(report["representation"], "named-ir;not-source")
        self.assertEqual(report["module"], "Data.Dictionary")
        self.assertEqual([d["name"] for d in report["declarations"]],
                         ["Dictionary", "MkDictionary", "useDictionary", "getCombine", "getIdentity"])
        self.assertTrue(all(d["generated"] for d in report["declarations"]))
        self.assertIn("Sigma", report["declarations"][0]["value"])
        self.assertIn("pair-case", report["declarations"][2]["value"])
        source = (ROOT / "examples/modules/record-projections/Data/Dictionary.fib").read_text()
        for declaration in report["declarations"]:
            span = declaration["origin"]
            self.assertEqual(source[span["start"]["offset"]:span["end"]["offset"]], declaration["name"])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Main.fib"
            # Unresolved imports and ill-typed bodies are deliberately not accepted/checked here.
            entry.write_text('module Main\nimport Missing\nmain : Bool\nmain = "wrong"\n')
            result = run("elaborate", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            self.assertNotEqual(run("check", "--source-dir", str(root), str(entry)).returncode, 0)
            # Syntax remains inspectable, while declaration admission is a separate failure.
            unsafe = ('module Main\nrecord R : Type 0 where\n'
                      '  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 y : Bool\n'
                      '  projection getX x\nmain : IO Unit\nmain = putStrLn "never"\n')
            entry.write_text(unsafe)
            result = run("symbols", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("getX", [s["name"] for s in json.loads(result.stdout)["symbols"]])
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            result = run("elaborate", str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Elaboration", result.stderr)
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "elaboration")
            self.assertEqual(diagnostic["path"], str(entry.resolve()))
            self.assertEqual(diagnostic["position"]["line"], 7)

    def test_explicit_interfaces_and_implementations(self):
        example = ROOT / "examples/modules/interfaces"
        result = run("run", "--source-dir", str(example), str(example / "Main.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, interfaces!\nExplicit dictionaries!\nMonoid shape!\n")
        report = json.loads(run("elaborate", str(example / "Algebra.fib")).stdout)
        self.assertFalse(report["checked"])
        self.assertEqual([d["name"] for d in report["declarations"][:4]],
                         ["Semigroup", "MkSemigroup", "useSemigroup", "combine"])
        self.assertTrue(all(d["generated"] for d in report["declarations"][:4]))
        inspected = json.loads(run("elaborate", str(example / "Instances/Text.fib")).stdout)
        self.assertTrue(all(d["implementation"] for d in inspected["declarations"]))
        # Definition targets are actual method tokens, not generated syntax.
        source = (example / "Algebra.fib").read_text()
        lines = source.splitlines()
        line = next(i + 1 for i, text in enumerate(lines) if "combine A dictionary" in text)
        column = lines[line - 1].index("combine A") + 1
        result = run("definition", "--source-dir", str(example), "--entry", str(example / "Main.fib"),
                     str(line), str(column), str(example / "Algebra.fib"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        location = json.loads(result.stdout)["definition"]
        self.assertEqual(location["path"], str((example / "Algebra.fib").resolve()))
        begin, end = location["range"]["start"]["offset"], location["range"]["end"]["offset"]
        self.assertEqual(source[begin:end], "combine")
        self.assertEqual(location["range"]["start"]["line"],
                         next(i + 1 for i, text in enumerate(lines) if text.startswith("  combine :")))

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"
            base = (
                'module Main\ninterface Flag : Type 0 where\n'
                '  constructor MkFlag\n  eliminator useFlag\n  flag : Bool\n'
                'implementation first : Flag\nfirst = MkFlag True\n'
                'implementation second : Flag\nsecond = MkFlag False\n'
                'main : IO Unit\nmain = putStrLn (if flag second then "true" else "false")\n')
            path.write_text(base)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "false\n")  # No automatic instance selection.
            formatted = run("format", str(path))
            self.assertEqual(formatted.returncode, 0, formatted.stderr)
            path.write_text(formatted.stdout)
            self.assertEqual(run("format", str(path)).stdout, formatted.stdout)
            for bad in (
                base.replace("second = MkFlag False", "second = MkFlag"),
                base.replace("second = MkFlag False", 'second = MkFlag "wrong"'),
                base.replace("  flag : Bool", "  1 flag : Bool"),
                base.replace("  flag : Bool", "  0 flag : Bool"),
                base.replace("  flag : Bool", "  flag : Bool\n  projection get flag"),
                base.replace("  flag : Bool", "  flag : Bool\n  flag : Bool"),
                base.replace("implementation second : Flag", "implementation 0 second : Flag"),
                base.replace("implementation second : Flag", "implementation first : Flag"),
                base.replace("module Main\n", ""),
                base.replace("implementation second", "implementation\nsecond"),
            ):
                path.write_text(bad)
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0, bad)
                self.assertEqual(result.stdout, "")
            # A named primitive alias is still not a structural dictionary.
            path.write_text('module Main\n0 Text : Type 0\nText = String\n'
                            'implementation wrong : Text\nwrong = "no"\n'
                            'main : IO Unit\nmain = putStrLn "never"\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("dictionary-shaped", result.stderr)
            self.assertEqual(result.stdout, "")
            # Introspection is expressly unchecked, even for this bad target.
            self.assertEqual(run("elaborate", str(path)).returncode, 0)
            # Quantities inside methods are invariant, not silently adapted.
            operation = (
                'module Main\ninterface Operation : Type 0 where\n'
                '  constructor MkOperation\n  eliminator useOperation\n'
                '  apply : (left : String) -> (right : String) -> String\n'
                'implementation operation : Operation\noperation = MkOperation appendString\n'
                'main : IO Unit\nmain = putStrLn (apply operation "explicit" " adapter")\n')
            path.write_text(operation)
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            path.write_text(operation.replace(
                "implementation operation",
                'adapter : (left : String) -> (right : String) -> String\n'
                'adapter = \\(left : String) => \\(right : String) => appendString left right\n'
                'implementation operation').replace("operation = MkOperation appendString", "operation = MkOperation adapter"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "explicit adapter\n")
            # All unused implementations are checked before publication/output.
            path.write_text(base.replace("second = MkFlag False", 'second = MkFlag "bad"')
                            .replace("flag second", "flag first"))
            self.assertNotEqual(run("run", "--source-dir", str(root), str(path)).returncode, 0)
            # Automatic method binders consume the normal declaration quota.
            fields = "".join(f"  method{i} : Bool\n" for i in range(62))
            path.write_text('module Main\ninterface TooMany : Type 0 where\n'
                            '  constructor MkTooMany\n  eliminator useTooMany\n' + fields)
            result = run("elaborate", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("budget", result.stderr)
            # Copy and format the actual imported example graph, then execute it.
            for original in example.rglob("*.fib"):
                destination = root / original.relative_to(example)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(original.read_bytes())
                formatted = run("format", str(destination))
                self.assertEqual(formatted.returncode, 0, formatted.stderr)
                destination.write_text(formatted.stdout)
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            # Private interface group members are not imported by guessing names.
            algebra = root / "Algebra.fib"
            algebra.write_text(algebra.read_text().replace("export\ninterface Semigroup", "interface Semigroup"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_singleton_records_and_dependent_elimination(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"

            def program(quantity, getter=True):
                return ('module Main\nrecord R : Type 0 where\n'
                        '  constructor MkR\n  eliminator useR\n'
                        '  ' + (quantity + ' ' if quantity else '') + 'value : String\n' +
                        ('  projection get value\n' if getter else '') +
                        'main : IO Unit\nmain = putStrLn (get (MkR "Singleton!"))\n')

            for quantity in ("1", ""):
                path.write_text(program(quantity))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "Singleton!\n")
                inspected = json.loads(run("elaborate", str(path)).stdout)
                self.assertFalse(inspected["checked"])
                formatted = run("format", str(path)).stdout
                path.write_text(formatted)
                self.assertEqual(run("format", str(path)).stdout, formatted)
            path.write_text(program("0"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Erased fields", result.stderr + result.stdout)
            self.assertEqual(result.stdout, "")
            path.write_text(program("0", False).replace(
                'putStrLn (get (MkR "Singleton!"))',
                'useR (\\(0 self : R) => IO Unit) (MkR "erased") (\\(0 value : String) => putStrLn "Erased!")'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Erased!\n")
            # Erased IO descriptions stored in a singleton never execute.
            path.write_text(
                'module Main\nrecord Actions : Type 0 where\n'
                '  constructor MkActions\n  eliminator useActions\n  0 action : IO Unit\n'
                'main : IO Unit\nmain = useActions (\\(0 self : Actions) => IO Unit) '
                '(MkActions (putStrLn "never")) (\\(0 action : IO Unit) => putStrLn "Only!")\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Only!\n")
            # An arbitrary dependent motive inspects an erased wrapped type.
            path.write_text(
                'module Main\nrecord Tag : Type 1 where\n'
                '  constructor MkTag\n  eliminator useTag\n  0 Item : Type 0\n'
                '0 itemType : (0 tag : Tag) -> Type 0\n'
                'itemType = \\(0 tag : Tag) => useTag (\\(0 self : Tag) => Type 0) tag (\\(0 Item : Type 0) => Item)\n'
                'identityFor : (1 tag : Tag) -> (1 x : itemType tag) -> itemType tag\n'
                'identityFor = \\(1 tag : Tag) => useTag (\\(0 self : Tag) => ((1 x : itemType self) -> itemType self : Type 1)) tag (\\(0 Item : Type 0) => \\(1 x : Item) => x)\n'
                'main : IO Unit\nmain = putStrLn (identityFor (MkTag String) "Dependent singleton!")\n')
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent singleton!\n")
            # Quantity-aware unary wrappers are not their naked payloads.
            path.write_text(program("1").replace('get (MkR "Singleton!")', 'MkR "Singleton!"'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            compatible = ('record S : Type 0 where\n  constructor MkS\n'
                          '  eliminator useS\n  1 other : String\n')
            source = program("1").replace("main : IO Unit", compatible + "main : IO Unit").replace(
                'get (MkR "Singleton!")', 'get (MkS "Singleton!")')
            path.write_text(source)
            self.assertEqual(run("run", "--source-dir", str(root), str(path)).stdout, "Singleton!\n")
            path.write_text(source.replace("  1 other : String", "  other : String"))
            self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)
            for body in ('"dropped"', 'appendString (get record) (get record)'):
                path.write_text(program("1").replace(
                    'main : IO Unit', 'bad : (1 record : R) -> String\n'
                    'bad = \\(1 record : R) => ' + body + '\nmain : IO Unit'))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_wider_dependent_records(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"

            def program(fields, requests="", body='putStrLn "unused"'):
                return ('module Main\nrecord R : Type 1 where\n'
                        '  constructor MkR\n  eliminator useR\n' +
                        "".join("  " + field + "\n" for field in fields) + requests +
                        'main : IO Unit\nmain = ' + body + '\n')

            # Third-field type depends on two distinct erased predecessors.
            fields = ["0 Item : Type 0", "0 flag : Bool",
                      "1 value : if flag then Item else Bool"]
            path.write_text(program(fields, "  projection get value\n",
                                    'putStrLn (get (MkR String True "Dependent!"))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Dependent!\n")
            # Dependent motive observes the complete reconstructed record.
            path.write_text(
                program(fields, "  projection get value\n", 'putStrLn (recover (MkR String True "Motive!"))')
                .replace('main : IO Unit',
                         '0 valueType : (0 r : R) -> Type 0\n'
                         'valueType = \\(0 r : R) => useR (\\(0 self : R) => Type 0) r '
                         '(\\(0 Item : Type 0) => \\(0 flag : Bool) => \\(1 value : if flag then Item else Bool) => if flag then Item else Bool)\n'
                         'recover : (1 r : R) -> valueType r\n'
                         'recover = \\(1 r : R) => useR (\\(0 self : R) => (valueType self : Type 1)) r '
                         '(\\(0 Item : Type 0) => \\(0 flag : Bool) => \\(1 value : if flag then Item else Bool) => value)\n'
                         'main : IO Unit'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Motive!\n")

            # Sparse transitive type dependencies in an eight-field telescope.
            fields = ["0 A : Type 0", "0 Family : (0 x : A) -> Type 0", "0 x : A",
                      "0 witness : Family x", "0 flag : Bool", "0 unused0 : Unit",
                      "0 unused1 : Unit", "1 value : Family x"]
            path.write_text(program(fields, "  projection get value\n",
                'putStrLn (get (MkR Unit (\\(0 x : Unit) => String) () "witness" True () () "Sparse!"))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Sparse!\n")
            # Late payload mismatches still reject before any effects.
            path.write_text(program(fields, "  projection get value\n",
                'putStrLn (get (MkR Unit (\\(0 x : Unit) => String) () "witness" True () () False))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

            # Every width, including eight fields, consumes every linear field.
            for width in list(range(2, 10)) + [12, 16]:
                names = [f"field{i}" for i in range(width)]
                fields = [f"1 {name} : String" for name in names]
                combine = names[-1]
                for name in reversed(names[:-1]):
                    combine = f"appendString {name} ({combine})"
                args = " ".join(f'"{i}"' for i in range(width))
                path.write_text(program(fields, body=f'useR (\\(0 self : R) => (IO Unit : Type 1)) (MkR {args}) '
                                        f'(\\(1 {names[0]} : String) => ' +
                                        "".join(f"\\(1 {name} : String) => " for name in names[1:]) +
                                        f'putStrLn ({combine}))'))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "".join(map(str, range(width))) + "\n")
                # No linear field may vanish in the generated branch.
                path.write_text(program(fields, body=f'useR (\\(0 self : R) => (IO Unit : Type 1)) (MkR {args}) '
                                        '(' + "".join(f"\\(1 {name} : String) => " for name in names) +
                                        f'putStrLn {names[0]})'))
                result = run("run", "--source-dir", str(root), str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

            # Erased extraction traverses past field eight; no fixed fuel of 8.
            fields = [f"0 tag{i} : Bool" for i in range(9)] + ["0 Item : Type 0", "1 value : Item"]
            path.write_text(program(fields, "  projection get value\n",
                                    'putStrLn (get (MkR True True True True True True True True True String "Long path!"))'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Long path!\n")

            # More than eight getter requests are ordinary declaration slots.
            # All nine independent getters remain within construction bounds.
            fields = [f"field{i} : Bool" for i in range(9)]
            requests = "".join(f"  projection get{i} field{i}\n" for i in range(9))
            path.write_text(program(fields, requests,
                                    'putStrLn (if get8 (MkR True True True True True True True True True) then "Getters!" else "bad")'))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Getters!\n")
            # Same normalized telescope, different record/field names: structural.
            compatible = (
                'record S : Type 1 where\n  constructor MkS\n  eliminator useS\n' +
                "".join(f"  other{i} : Bool\n" for i in range(9)))
            path.write_text(program(fields, requests,
                                    'putStrLn (if get8 (MkS True True True True True True True True True) then "Structural!" else "bad")')
                            .replace("main : IO Unit", compatible + "main : IO Unit"))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "Structural!\n")
            for bad_fields in ([],
                               ["first : Bool", "second : Bool", "first : String"]):
                path.write_text(program(bad_fields))
                self.assertNotEqual(run("check", "--source-dir", str(root), str(path)).returncode, 0)
            # A getter must reject a discarded linear field anywhere in the tail.
            fields = ["0 Item : Type 0", "0 flag : Bool", "1 kept : String", "1 lost : String"]
            path.write_text(program(fields, "  projection get kept\n"))
            result = run("check", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("linear", result.stderr + result.stdout)

    def test_record_construction_admission_not_field_cap(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Main.fib"

            def record(name, width):
                return (f"record {name} : Type 0 where\n  constructor Mk{name}\n  eliminator use{name}\n" +
                        "".join(f"  field{i} : Bool\n" for i in range(width)))

            # Syntax-only tools retain an oversized telescope without expanding it.
            source = "module Main\n" + record("R", 200) + 'main : IO Unit\nmain = putStrLn "never"\n'
            path.write_text(source)
            self.assertEqual(run("symbols", str(path)).returncode, 0)
            self.assertEqual(run("format", str(path)).returncode, 0)
            result = run("check", "--json", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertTrue(any(d["stage"] == "elaboration" and
                                "construction budget exhausted" in d["message"]
                                for d in report["diagnostics"]))
            result = run("run", "--source-dir", str(root), str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # The construction allowance is cumulative, not reset for each record.
            path.write_text("module Main\n" + "".join(record(f"R{i}", 32) for i in range(7)) +
                            "main : Bool\nmain = True\n")
            result = run("elaborate", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("construction budget exhausted", result.stdout + result.stderr)

    def test_safe_record_projections(self):
        root = "examples/modules/record-projections"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Safe projections!\n")
        result = run("eval", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Safe projections!")', result.stdout)
        with tempfile.TemporaryDirectory(prefix="projections ") as directory:
            target = Path(directory)
            entry = target / "Main.fib"
            def program(first, second, requests, body, result_type="IO Unit"):
                return ('module Main\nrecord R : Type 0 where\n'
                        '  constructor MkR\n  eliminator useR\n'
                        f'  {first}\n  {second}\n' +
                        "".join(f"  projection {name} {field}\n" for name, field in requests) +
                        f'main : {result_type}\nmain = {body}\n')
            # Both positions, all permitted discard/selection quantity combinations.
            for left in ("0 left : Bool", "1 left : Bool", "left : Bool"):
                for right in ("0 right : Bool", "1 right : Bool", "right : Bool"):
                    for selected in ("left", "right"):
                        selected_decl = left if selected == "left" else right
                        other_decl = right if selected == "left" else left
                        allowed = not selected_decl.startswith("0 ") and not other_decl.startswith("1 ")
                        entry.write_text(program(left, right, [("get", selected)],
                                                 'putStrLn (if get (MkR True False) then "true" else "false")'))
                        result = run("run", "--source-dir", str(target), str(entry))
                        if allowed:
                            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                            self.assertEqual(result.stdout, "true\n" if selected == "left" else "false\n")
                        else:
                            self.assertNotEqual(result.returncode, 0)
                            self.assertEqual(result.stdout, "")
            # A getter consumes its record, even when its fields are reusable.
            entry.write_text(program("left : Bool", "right : Bool",
                                     [("getLeft", "left"), ("getRight", "right")],
                                     'putStrLn "never"').replace(
                'main : IO Unit',
                'bad : (1 record : R) -> Bool\n'
                'bad = \\(1 record : R) => andBool (getLeft record) (getRight record)\n'
                'main : IO Unit'))
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # The second result type genuinely depends on an erased first field.
            entry.write_text(program(
                "0 flag : Bool", "1 value : if flag then String else Bool", [("getValue", "value")],
                'putStrLn (getValue (MkR True "dependent"))'))
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "dependent\n")
            for requests in ([("get", "missing")], [("get", "left"), ("get", "right")],
                             [(f"get{i}", "left") for i in range(61)]):
                entry.write_text(program("left : Bool", "right : Bool", requests, 'putStrLn "never"'))
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # Dependent parameterized second-field projection, across a module boundary.
            library = target / "Library.fib"
            library_source = ('module Library\nexport\nrecord Box (0 A : Type 0) : Type 0 where\n'
                              '  constructor MkBox\n  eliminator useBox\n'
                              '  0 tag : Unit\n  1 value : A\n  projection payload value\n')
            library.write_text(library_source)
            entry.write_text('module Main\nimport Library\nmain : IO Unit\n'
                             'main = putStrLn (Library.payload String (Library.MkBox String () "imported"))\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "imported\n")
            source = entry.read_text()
            offset = source.index("payload")
            point = source[:offset].rsplit("\n", 1)[-1]
            result = run("definition", "--source-dir", str(target), "--entry", str(entry),
                         "4", str(len(point) + 1), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            location = json.loads(result.stdout)["definition"]
            self.assertEqual(location["path"], str(library.resolve()))
            self.assertEqual(library_source[location["range"]["start"]["offset"]:
                                            location["range"]["end"]["offset"]], "payload")
            library.write_text(library_source.replace("export\nrecord", "record"))
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Unbound name", result.stderr)

    def test_consuming_record_patterns(self):
        root = "examples/modules/records"
        result = run("run", "--source-dir", root, root + "/Patterns.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Patterns!\n")
        result = run("eval", "--source-dir", root, root + "/Patterns.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Patterns!")', result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            header = "module Main\nimport Data.Message\nmain : IO Unit\nmain = putStrLn "
            prefix = ('(case Data.Message.MkMessage True "payload" return '
                      '(\\(0 self : Data.Message.Message) => String) of ')
            failures = [
                '(1 loud : Bool) (1 text : String) => text)',
                '(1 loud : Bool) (1 text : String) => if loud then appendString text text else text)',
                '(loud : Bool) (text : String) => if loud then text else text)',
                '(1 _ : Bool) (1 text : String) => text)',
                '(1 loud : Bool) (1 text : Bool) => if loud then "wrong" else "wrong")',
                '(1 same : Bool) (1 same : String) => same)',
                '(1 loud : Bool) => "missing")',
                '(1 loud : Bool) (1 text : String) (1 extra : Unit) => text)',
            ]
            for body in failures:
                entry.write_text(header + prefix + body + "\n")
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0, body)
                self.assertEqual(result.stdout, "")
            # Erased wildcards are allowed; linear wildcards above cannot discard.
            entry.write_text(
                'module Main\nrecord Marked : Type 0 where\n  constructor MkMarked\n'
                '  eliminator useMarked\n  0 mark : Unit\n  1 value : String\n'
                'main : IO Unit\nmain = putStrLn (case MkMarked () "wildcard" return '
                '(\\(0 self : Marked) => String) of (0 _ : Unit) (1 value : String) => value)\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "wildcard\n")
            # Motive is outside pattern scope, not re-resolved after binding.
            entry.write_text(header + '(case Data.Message.MkMessage True "x" return missing of '
                             '(1 missing : Bool) (1 text : String) => if missing then text else text)\n')
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Unbound name "missing"', result.stderr)
            # Shared lexical traversal identifies authored pattern binders, not synthetic spans.
            source = ('case unknown return (\\(0 self : Unknown) => String) of\n'
                      '  (0 A : Type 0) (1 value : A) => value\n')
            entry.write_text(source)
            offset = source.rindex("value")
            line = source[:offset].count("\n") + 1
            column = len(source[:offset].rsplit("\n", 1)[-1]) + 1
            result = run("definition", str(line), str(column), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            span = json.loads(result.stdout)["definition"]
            self.assertEqual(span["start"]["offset"], source.index("value :"))
            domain = source.index("A) =>")
            result = run("definition", "2", str(len(source[:domain].rsplit("\n", 1)[-1]) + 1), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            span = json.loads(result.stdout)["definition"]
            self.assertEqual(span["start"]["offset"], source.index("A :"))
            # Rename is lexical only and preserves the pattern scopes.
            result = run("rename-preview", str(line), str(column), "payload", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(len(json.loads(result.stdout)["edits"]), 2)

    def test_record_parameter_telescopes(self):
        root = "examples/modules/record-parameters"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Record parameters!\n")
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            # Value indices, not only Type parameters; branch types specialize.
            flagged = ('module Main\nrecord Flagged (0 flag : Bool) : Type 0 where\n'
                       '  constructor MkFlagged\n  eliminator useFlagged\n'
                       '  0 tag : Unit\n  1 payload : if flag then String else Bool\n')
            entry.write_text(flagged + 'main : IO Unit\nmain = putStrLn '
                             '(useFlagged True (\\(0 self : Flagged True) => String) '
                             '(MkFlagged True () "indexed") (\\(0 tag : Unit) => \\(1 payload : String) => payload))\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "indexed\n")
            bad_programs = [
                flagged + 'main : Flagged False\nmain = MkFlagged False () "wrong"\n',
                flagged + 'bad : (0 flag : Bool) -> Bool\n'
                'bad = \\(0 flag : Bool) => flag\nmain : IO Unit\nmain = putStrLn "never"\n',
                'module Main\nrecord R (0 B : A) (0 A : Type 0) : Type 0 where\n'
                '  constructor MkR\n  eliminator useR\n  1 x : Bool\n  1 y : Bool\n'
                'main : IO Unit\nmain = putStrLn "never"\n',
                'module Main\nimport Data.AppendDictionary\nmain : IO Unit\n'
                'main = putStrLn (Data.AppendDictionary.appendWith String '
                '(Data.AppendDictionary.MkAppendDictionary String appendString "") "a" "b")\n',
                'module Main\nimport Data.Indexed\nmain : IO Unit\n'
                'main = putStrLn (Data.Indexed.MkIndexed True True True "bad")\n',
            ]
            for source in bad_programs:
                entry.write_text(source)
                result = run("check", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # Parameters can equal global declaration names without capture.
            entry.write_text(
                'module Main\nrecord Capture (0 Capture : Type 0) (0 MkCapture : Type 0) : Type 0 where\n'
                '  constructor MkCapture\n  eliminator useCapture\n'
                '  1 left : Capture\n  1 right : MkCapture\n'
                'main : Capture String Bool\nmain = MkCapture String Bool "left" True\n')
            result = run("eval", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('"left"', result.stdout)
            # A reusable dictionary works at Bool too; methods/identity are data.
            entry.write_text(
                'module Main\nimport Data.AppendDictionary\n'
                'both : (left : Bool) -> (right : Bool) -> Bool\n'
                'both = \\(left : Bool) => \\(right : Bool) => andBool left right\n'
                'main : IO Unit\nmain = putStrLn (if Data.AppendDictionary.appendWith Bool '
                '(Data.AppendDictionary.MkAppendDictionary Bool both True) True False then "wrong" else "bool")\n')
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "bool\n")

    def test_named_dependent_records(self):
        root = "examples/modules/records"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Records!\n")
        result = run("eval", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Records!")', result.stdout)
        entry_text = (ROOT / root / "Main.fib").read_text()
        point = entry_text.index("MkMessage")
        line = entry_text[:point].count("\n") + 1
        column = len(entry_text[:point].rsplit("\n", 1)[-1]) + 1
        result = run("definition", "--source-dir", root, "--entry", root + "/Main.fib",
                     str(line), str(column), root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        definition = json.loads(result.stdout)["definition"]
        self.assertEqual(definition["path"], str((ROOT / root / "Data/Message.fib").resolve()))
        message_text = (ROOT / root / "Data/Message.fib").read_text()
        self.assertEqual(message_text[definition["range"]["start"]["offset"]:
                                      definition["range"]["end"]["offset"]], "MkMessage")
        with tempfile.TemporaryDirectory(prefix="records ") as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            message = target / "Data/Message.fib"
            package = target / "Data/Package.fib"
            original_message = message.read_text()
            original_package = package.read_text()
            header = "module Main\nimport Data.Package\nimport Data.Message\nmain : IO Unit\nmain = "
            for body in (
                'putStrLn (Data.Package.recover (Data.Package.MkPackage Bool "wrong"))',
                'putStrLn (Data.Message.render (Data.Message.MkMessage True True))',
                'putStrLn (Data.Message.consumeMessage (\\(0 self : Data.Message.Message) => String) '
                '(Data.Message.MkMessage True "text") (\\(1 loud : Bool) => \\(1 text : String) => text))',
                'putStrLn (Data.Message.consumeMessage (\\(0 self : Data.Message.Message) => String) '
                '(Data.Message.MkMessage True "text") (\\(loud : Bool) => \\(text : String) => text))',
                'putStrLn (Data.Package.unpackPackage (\\(0 self : Data.Package.Package) => (String : Type 1)) '
                '(Data.Package.MkPackage Bool True) (\\(0 Item : Type 0) => \\(1 value : Item) => value))',
            ):
                entry.write_text(header + body + "\n")
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            entry.write_bytes((ROOT / root / "Main.fib").read_bytes())
            message.write_text(original_message.replace("export\nrecord", "record"))
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unbound name", result.stderr)
            message.write_text(original_message)
            # Constructor and record names can coincide with field names without capture.
            package.write_text(
                "module Data.Package\nexport\nrecord Package : Type 1 where\n"
                "  constructor MkPackage\n  eliminator unpackPackage\n"
                "  0 Package : Type 0\n  1 MkPackage : Package\n")
            entry.write_text('module Main\nimport Data.Package\nmain : IO Unit\n'
                             'main = putStrLn (Data.Package.unpackPackage '
                             '(\\(0 self : Data.Package.Package) => (String : Type 1)) '
                             '(Data.Package.MkPackage String "ok") '
                             '(\\(0 A : Type 0) => \\(1 value : A) => '
                             'case () of () => "bad"))\n')
            # This branch drops a linear payload; name-collision lowering itself checks.
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            entry.write_text('module Main\nimport Data.Package\n'
                             'main : Data.Package.Package\nmain = Data.Package.MkPackage String "ok"\n')
            result = run("eval", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('"ok"', result.stdout)
            package.write_text(original_package.replace("record Package : Type 1", "record Package : Type 0"))
            result = run("check", "--source-dir", str(target), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            package.write_text(original_package)
            # Reachable dependencies are checked, including unused record definitions.
            entry.write_bytes((ROOT / root / "Main.fib").read_bytes())
            for replacement in (
                original_message + "\nrecord Unused : Type 0 where\n  constructor MkUnused\n  eliminator useUnused\n  1 x : Bool\n  1 y : missing\n",
                original_message.replace("1 text : String", "1 text : missing"),
                original_message.replace("  1 text : String", "  1 text : String\n  1 extra : Bool"),
                original_message.replace("  1 text : String", "  1 loud : String"),
                original_message.replace("  eliminator consumeMessage", "eliminator consumeMessage"),
            ):
                message.write_text(replacement)
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

            # Initial named records are transparent structural abbreviations.
            entry.write_text(
                'module Main\nrecord First : Type 0 where\n  constructor MkFirst\n'
                '  eliminator useFirst\n  1 flag : Bool\n  1 text : String\n'
                'record Second : Type 0 where\n  constructor MkSecond\n'
                '  eliminator useSecond\n  1 other : Bool\n  1 value : String\n'
                'main : Second\nmain = MkFirst True "structural"\n')
            result = run("eval", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('"structural"', result.stdout)

    def test_staged_erased_module_globals(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library = root / "Types.fib"
            entry = root / "Main.fib"
            source = ('module Types\nexport\n0 Bit : Type 0\nBit = Bool\n'
                      'export\n0 Alias : Type 0\nAlias = Types.Bit\n'
                      'export\n0 secret : Bool\nsecret = True\n'
                      'export\n0 text : String\ntext = "hidden"\n'
                      'export\n0 Choose : (0 bit : Bool) -> Type 0\n'
                      'Choose = \\(0 bit : Bool) => if bit then String else Bool\n')
            library.write_text(source, encoding="utf-8")
            entry.write_text(
                'module Main\nimport Types\nvalue : Types.Alias\nvalue = True\n'
                'identity : (0 A : Type 0) -> (1 x : A) -> A\n'
                'identity = \\(0 A : Type 0) => \\(1 x : A) => x\n'
                'message : Types.Choose True\nmessage = "staged"\n'
                'other : Types.Choose False\nother = True\n'
                'main : IO Unit\nmain = putStrLn (if identity Types.Alias value then message else "wrong")\n',
                encoding="utf-8")
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "staged\n")
            # Erased data may be passed to an erased parameter.
            entry.write_text(
                'module Main\nimport Types\nignore : (0 bit : Bool) -> String\n'
                'ignore = \\(0 bit : Bool) => "ignored"\n'
                'main : IO Unit\nmain = putStrLn (ignore Types.secret)\n', encoding="utf-8")
            self.assertEqual(run("run", "--source-dir", str(root), str(entry)).stdout, "ignored\n")
            for body in ('putStrLn Types.text', 'putStrLn (if Types.secret then "leak" else "")',
                         'bind Bool Unit (pure Bool Types.secret) (\\(1 bit : Bool) => putStrLn (if bit then "leak" else ""))'):
                entry.write_text('module Main\nimport Types\nmain : IO Unit\nmain = ' + body + '\n',
                                 encoding="utf-8")
                for command in ("check", "eval", "run"):
                    result = run(command, "--source-dir", str(root), str(entry))
                    self.assertNotEqual(result.returncode, 0, result.stdout)
                    self.assertEqual(result.stdout, "")
            entry.write_text('module Main\nimport Types\nmain : IO Unit\nmain = putStrLn "safe"\n',
                             encoding="utf-8")
            library.write_text(source + '0 broken : Bool\nbroken = "wrong"\n', encoding="utf-8")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            self.assertEqual(report["diagnostics"][0]["stage"], "erased-checking")
            self.assertEqual(report["diagnostics"][0]["path"], str(library.resolve()))
            self.assertIsNone(report["diagnostics"][0]["position"])
            library.write_text(source, encoding="utf-8")
            # Headerless local typed-let opacity has not changed.
            entry.write_text('import Types\nmain : IO Unit\nmain = putStrLn Types.text\n', encoding="utf-8")
            self.assertNotEqual(run("run", "--source-dir", str(root), str(entry)).returncode, 0)
            entry.write_text('module Main\n0 main : Bool\nmain = True\n', encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("main must be unrestricted", result.stderr)

    def test_explicit_generic_operation_profiles(self):
        root = "examples/modules/operations"
        result = run("run", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\n")
        result = run("eval", "--source-dir", root, root + "/Main.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Hello, Fibril!")', result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory)
            for path in (ROOT / root).rglob("*.fib"):
                destination = target / path.relative_to(ROOT / root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(path.read_bytes())
            entry = target / "Main.fib"
            failures = [
                ('module Main\nimport Algebra.Operation\nmain : IO Unit\n'
                 'main = putStrLn (Algebra.Operation.combineThree String appendString "a" "b" "c")\n'),
                ('module Main\nimport Algebra.Operation\nimport Instances.Text\n'
                 'bad : (1 text : String) -> String\n'
                 'bad = \\(1 text : String) => Algebra.Operation.combineThree String Instances.Text.append text "" ""\n'
                 'main : IO Unit\nmain = putStrLn "must not execute"\n'),
                ('module Main\nAlias : Type 0\nAlias = String\n'
                 'main : IO Unit\nmain = putStrLn "must not execute"\n'),
                ('module Main\n0 secret : String\nsecret = "must not execute"\n'
                 'main : IO Unit\nmain = putStrLn secret\n'),
            ]
            for source in failures:
                entry.write_text(source, encoding="utf-8")
                result = run("run", "--source-dir", str(target), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            # An operation profile alone does not enforce associativity.
            entry.write_text(
                'module Main\nimport Algebra.Operation\n'
                'nand : (left : Bool) -> (right : Bool) -> Bool\n'
                'nand = \\(left : Bool) => \\(right : Bool) => notBool (andBool left right)\n'
                'main : IO Unit\n'
                'main = putStrLn (if Algebra.Operation.combineThree Bool nand True True False then "shape only" else "unexpected")\n',
                encoding="utf-8")
            result = run("run", "--source-dir", str(target), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "shape only\n")

    def test_builtin_and_prelude_references(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Reference.fib"
            def reference(source, token, skip=0):
                path.write_text(source, encoding="utf-8")
                offset = source.index(token) + skip
                line = source[:offset].count("\n") + 1
                column = len(source[:offset].rsplit("\n", 1)[-1]) + 1
                result = run("reference", str(line), str(column), str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                return json.loads(result.stdout)["reference"]
            for name in ("String", "Unit", "Bool", "Type"):
                target = reference(name + (" 0" if name == "Type" else ""), name)
                self.assertEqual(target["kind"], "builtin-documentation")
                self.assertEqual(target["name"], name)
                self.assertNotIn("range", target)
            target = reference("IO Unit", "IO")
            self.assertEqual(target["kind"], "builtin-documentation")
            self.assertIn("Compiler primitive", " ".join(target["lines"]))
            for name in ("putStrLn", "pure", "bind", "map", "appendString"):
                target = reference(name, name)
                self.assertEqual(target["kind"], "bundled-prelude-source")
                source = target["source"]
                start = target["range"]["start"]["offset"]
                end = target["range"]["end"]["offset"]
                self.assertEqual(source[start:end], name)
                self.assertTrue(source[end:].startswith(" ="))
                self.assertEqual(source, (ROOT / "stdlib/Prelude.fib").read_text())
            for source, token, skip in [
                ('"String IO putStrLn"', "IO", 0),
                ("-- IO\nTrue", "IO", 0),
                ("\\(1 IO : String) => IO", "=> IO", 3),
                ("putStrLn : String\nputStrLn = \"local\"\nmain : String\nmain = putStrLn",
                 "main = putStrLn", 7),
                ("Text.putStrLn", "putStrLn", 0),
            ]:
                self.assertIsNone(reference(source, token, skip))

    def test_checked_project_definition_queries(self):
        for ending in ("\n", "\r\n"):
            with self.subTest(ending=ending), tempfile.TemporaryDirectory(prefix="definitions 'quoted' ") as directory:
                root = Path(directory)
                (root / "Text").mkdir()
                entry = root / "Main.fib"
                library = root / "Text/Greeting.fib"
                shared = root / "Shared.fib"
                sources = {
                    entry: ('-- 🌍e\u0301\nmodule Main\nimport Text.Greeting\nmain : IO Unit\n'
                            'main = let (1 Text : String) = "local" in (Text.Greeting.greet) Text\n'),
                    library: ('module Text.Greeting\nimport Shared\n'
                              'helper : (1 value : String) -> String\n'
                              'helper = \\(1 value : String) => appendString "prefix" value\n'
                              'export\ngreet : (1 text : String) -> IO Unit\n'
                              'greet = \\(1 text : String) => putStrLn (Text.Greeting.helper (appendString Shared.message text))\n'),
                    shared: 'module Shared\nexport\nmessage : String\nmessage = "shared"\n',
                }
                sources = {path: text.replace("\n", ending) for path, text in sources.items()}
                for path, text in sources.items():
                    path.write_bytes(text.encode("utf-8"))

                def point(text, offset):
                    return {"offset": offset, "line": text[:offset].count("\n") + 1,
                            "column": len(text[:offset].rsplit("\n", 1)[-1]) + 1}

                def query(path, text, token, skip=0):
                    position = point(text, text.index(token) + skip)
                    result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                                 str(position["line"]), str(position["column"]), str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stderr, "")
                    report = json.loads(result.stdout)
                    self.assertEqual(report["version"], 2)
                    self.assertTrue(report["checked"])
                    self.assertEqual(report["query"], str(path.resolve()))
                    self.assertEqual({s["path"]: s["text"] for s in report["sources"]},
                                     {str(p.resolve()): t for p, t in sources.items()})
                    return report["definition"]

                def expect(target, path, token):
                    self.assertEqual(target["path"], str(path.resolve()))
                    start = sources[path].index(token)
                    self.assertEqual(target["range"]["start"], point(sources[path], start))
                    name = token.split()[0]
                    self.assertEqual(target["range"]["end"], point(sources[path], start + len(name)))

                expect(query(entry, sources[entry], "Text.Greeting.greet", len("Text.Greeting.")),
                       library, "greet =")
                # Query a library without inventing its own main.
                expect(query(library, sources[library], "Text.Greeting.helper", len("Text.Greeting.")),
                       library, "helper =")
                expect(query(library, sources[library], "Shared.message", len("Shared.")),
                       shared, "message =")
                # The local Text binder does not capture the qualified namespace.
                local = query(entry, sources[entry], ") Text", 2)
                self.assertEqual(local["path"], str(entry.resolve()))
                self.assertEqual(local["range"]["start"],
                                 point(sources[entry], sources[entry].index("Text :")))
                for token, skip in (("Text.Greeting.greet", 0), ("Text.Greeting.greet", len("Text")),
                                    ('"local"', 1), ("import Text", 7)):
                    self.assertIsNone(query(entry, sources[entry], token, skip))
                self.assertIsNone(query(library, sources[library], "putStrLn"))
                outside = root / "Unreachable.fib"
                outside.write_text("module Unreachable\n", encoding="utf-8")
                result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                             "1", "1", str(outside))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("not in the checked project graph", result.stderr)
                for replacement in ("Text.Greeting.helper", "Shared.message"):
                    entry.write_text("module Main\nimport Text.Greeting\nmain : String\nmain = " +
                                     replacement + "\n", encoding="utf-8")
                    result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                                 "4", "8", str(entry))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                entry.write_bytes(sources[entry].encode("utf-8"))
                # No successful navigation packet is emitted for an invalid unused body.
                shared.write_text('module Shared\nexport\nmessage : String\nmessage = "shared"\n'
                                  'unused : Bool\nunused = "wrong"\n', encoding="utf-8")
                result = run("definition", "--source-dir", str(root), "--entry", str(entry),
                             "1", "1", str(library))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(str(shared.resolve()), result.stderr)

    def test_project_json_source_provenance(self):
        with tempfile.TemporaryDirectory(prefix="project json ") as directory:
            root = Path(directory)
            entry = root / "Main.fib"
            dependency = root / "Library.fib"
            entry_source = ('module Main\nimport Library\nmain : IO Unit\n'
                            'main = Library.output\n')
            dependency_source = ('-- 🌍\r\nmodule Library\r\nexport\r\noutput : IO Unit\r\n'
                                 'output = putStrLn "not executed"\r\n')
            entry.write_text(entry_source, encoding="utf-8")
            dependency.write_bytes(dependency_source.encode("utf-8"))
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            report = json.loads(result.stdout)
            self.assertEqual(report["version"], 2)
            self.assertTrue(report["accepted"])
            self.assertEqual(report["entry"], str(entry.resolve()))
            self.assertEqual(report["root"], str(root.resolve()))
            self.assertEqual(report["diagnostics"], [])
            self.assertEqual({s["path"]: s["text"] for s in report["sources"]}, {
                str(entry.resolve()): entry_source, str(dependency.resolve()): dependency_source})
            self.assertNotIn("\nnot executed\n", result.stdout)
            self.assertEqual(result.stderr, "")
            # A dependency resolver point must never become an entry-file point.
            bad = '-- 🌍\r\nmodule Library\r\nexport\r\noutput : IO Unit\r\noutput = missing\r\n'
            dependency.write_bytes(bad.encode("utf-8"))
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["path"], str(dependency.resolve()))
            self.assertEqual(diagnostic["stage"], "resolution")
            self.assertTrue(diagnostic["sourceAvailable"])
            self.assertEqual(diagnostic["position"], {
                "offset": bad.index("missing"), "line": 5, "column": 10})
            self.assertEqual({s["path"]: s["text"] for s in report["sources"]}[diagnostic["path"]], bad)
            dependency.write_text('module Library\nexport\noutput : IO Unit\noutput = True\n', encoding="utf-8")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["path"], str(dependency.resolve()))
            self.assertEqual(diagnostic["stage"], "runtime-checking")
            self.assertIsNone(diagnostic["position"])
            self.assertIsNone(diagnostic["byteOffset"])
            self.assertTrue(diagnostic["sourceAvailable"])
            dependency.write_bytes("🌍".encode("utf-8") + b"\xff")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "decoding")
            self.assertEqual(diagnostic["path"], str(dependency.resolve()))
            self.assertEqual(diagnostic["byteOffset"], 4)
            self.assertIsNone(diagnostic["position"])
            self.assertFalse(diagnostic["sourceAvailable"])
            self.assertEqual(report["sources"], [])
            dependency.write_text("\u202e", encoding="utf-8")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "source-validation")
            self.assertEqual(diagnostic["position"], {"offset": 0, "line": 1, "column": 1})
            self.assertFalse(diagnostic["sourceAvailable"])
            dependency.unlink()
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            diagnostic = report["diagnostics"][0]
            self.assertEqual(diagnostic["path"], str(entry.resolve()))
            self.assertEqual(diagnostic["position"]["line"], 2)
            self.assertTrue(diagnostic["sourceAvailable"])
            self.assertEqual(len(report["sources"]), 1)
            # Known empty text is not the same as an unavailable source snapshot.
            entry.write_bytes(b"")
            result = run("check", "--json", "--source-dir", str(root), str(entry))
            report = json.loads(result.stdout)
            self.assertFalse(report["accepted"])
            self.assertEqual(report["sources"], [{"path": str(entry.resolve()), "text": ""}])
            self.assertTrue(report["diagnostics"][0]["sourceAvailable"])

    def test_module_execution_and_evaluation(self):
        root = "examples/modules/checked"
        entry = root + "/Main.fib"
        result = run("run", "--source-dir", root, entry)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\n")
        self.assertEqual(result.stderr, "")
        result = run("eval", "--source-dir", root, entry)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Hello, Fibril!")', result.stdout)
        self.assertNotIn("\nHello, Fibril!\n", result.stdout)
        result = run("eval", "--source-dir", root, "--fuel", "0", entry)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("budget exhausted", result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            dependency = root / "Library.fib"
            entry = root / "Main.fib"
            dependency.write_text(
                "module Library\nexport\nidentity : (0 A : Type 0) -> (1 x : A) -> A\n"
                "identity = \\(0 A : Type 0) => \\(1 x : A) => x\n",
                encoding="utf-8")
            entry.write_text(
                'module Main\nimport Library\nmain : String\n'
                'main = Library.identity String "pure result"\n', encoding="utf-8")
            result = run("eval", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: "pure result"', result.stdout)
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("IO Unit", result.stderr)
            # A later invalid plan is fully prepared before any writes.
            body = ('module Main\nimport Library\nmain : IO Unit\nmain = do\n'
                    '  putStrLn "must not print"\n')
            entry.write_text(body + '  putStrLn True\n', encoding="utf-8")
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            # A bad unused dependency definition also prevents all output.
            dependency.write_text(
                "module Library\nunused : Bool\nunused = \"wrong\"\n", encoding="utf-8")
            entry.write_text('module Main\nimport Library\nmain : IO Unit\n'
                             'main = putStrLn "must not print"\n', encoding="utf-8")
            for command in ("eval", "run"):
                result = run(command, "--source-dir", str(root), str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(str(dependency.resolve()), result.stderr)
                self.assertNotIn("^", result.stderr)
            dependency.write_text("module Library\n", encoding="utf-8")
            # Runtime action cap remains separate from successful project checking.
            entry.write_text(
                'module Main\nimport Library\ntwice : IO Unit\ntwice = do\n'
                '  putStrLn "never"\n  putStrLn "never"\n'
                'main : IO Unit\nmain = do\n' + '  twice\n' * 33, encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("run", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("output action count limit", result.stderr)
            for fuel in ("-1", "4097", "x"):
                result = run("eval", "--source-dir", str(root), "--fuel", fuel, str(entry))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("Fuel", result.stderr)

    def test_checked_module_interfaces(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def module(name, imports=(), body=""):
                path = root.joinpath(*name.split(".")).with_suffix(".fib")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("module " + name + "\n" +
                                "".join("import " + value + "\n" for value in imports) + body,
                                encoding="utf-8")
                return path
            library = module("Text.Greeting", body=(
                'hidden : String\nhidden = "private"\n'
                'export\ngreet : (1 text : String) -> IO Unit\n'
                'greet = \\(1 text : String) => putStrLn (appendString hidden text)\n'
                'export\nidentity : (0 A : Type 0) -> (1 x : A) -> A\n'
                'identity = \\(0 A : Type 0) => \\(1 x : A) => x\n'))
            entry = module("Main", ("Text.Greeting",), (
                'main : IO Unit\nmain = Text.Greeting.greet '
                '(Text.Greeting.identity String " must not print")\n'))
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Type: (IO Unit)", result.stdout)
            self.assertNotIn("must not print", result.stdout)
            self.assertEqual(result.stderr, "")
            module("Main", ("Text.Greeting",),
                   'main : IO Unit\nmain = do (Unit)\n'
                   '  let (1 original : String) = "block"\n'
                   '  (1 text : String) <- pure String (Text.Greeting.identity String original)\n'
                   '  Text.Greeting.greet (text : String)\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            entry = module("Main", ("Text.Greeting",),
                           'main : String\nmain = Text.Greeting.hidden\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Unbound name", result.stderr)
            self.assertIn(str(entry.resolve()), result.stderr)
            # Transitive modules are not implicitly visible.
            module("Bridge", ("Text.Greeting",), 'export\nvalue : Bool\nvalue = True\n')
            module("Main", ("Bridge",), 'main : Bool\nmain = Text.Greeting.identity Bool True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unbound name", result.stderr)
            # Equal leaf names remain distinct qualified exports.
            module("First", body='export\nvalue : Bool\nvalue = True\n')
            module("Second", body='export\nvalue : String\nvalue = "second"\n')
            module("Main", ("First", "Second"),
                   'main : String\nmain = if First.value then Second.value else "no"\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Type: String", result.stdout)
            # Earlier private definitions may use the current module's qualifier.
            module("First", body='private : Bool\nprivate = True\nexport\nvalue : Bool\nvalue = First.private\n')
            self.assertEqual(run("check", "--source-dir", str(root), str(entry)).returncode, 0)
            # Invalid private definitions fail before any interface is published.
            library = module("First", body='unused : Bool\nunused = "bad"\nexport\nvalue : Bool\nvalue = True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(library.resolve()), result.stderr)
            self.assertNotIn("^", result.stderr)  # no invented core-error source point
            module("First", body='1 secret : Bool\nsecret = True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unrestricted", result.stderr)
            module("Main", (), 'other : Bool\nother = True\n')
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("own main", result.stderr)
            # Anonymous entry keeps existing local-let/quantity semantics.
            entry.write_text('main : Bool\nmain = True\n', encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            entry.write_text("0 Bit : Type 0\nBit = Bool\nmain : Bit\nmain = True\n", encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)

    def test_module_expansion_budget(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "M0.fib").write_text(
                "module M0\nexport\nf : Bool -> Bool\nf = \\(x : Bool) => x\n", encoding="utf-8")
            for index in range(1, 16):
                (root / f"M{index}.fib").write_text(
                    f"module M{index}\nimport M{index - 1}\nexport\nf : Bool -> Bool\n"
                    f"f = \\(x : Bool) => andBool (M{index - 1}.f x) (M{index - 1}.f x)\n",
                    encoding="utf-8")
            entry = root / "Main.fib"
            entry.write_text("module Main\nimport M15\nmain : Bool\nmain = M15.f True\n", encoding="utf-8")
            result = run("check", "--source-dir", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Expanded core construction budget", result.stderr)

    def test_qualified_reference_syntax(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Library.fib").write_text(
                "module Library\nexport\nvalue : String\nvalue = \"data\"\n", encoding="utf-8")
            entry = root / "Main.fib"
            entry.write_text(
                "module Main\nimport Library\nmain : String\nmain = Library.value\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)["checked"])
            result = run("symbols", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("definition", "4", "8", str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIsNone(json.loads(result.stdout)["definition"])
            result = run("check", str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Module checking requires --source-dir", result.stdout)
            entry.write_text("Library.value\n", encoding="utf-8")
            result = run("check", "--json", str(entry))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "resolution")
            self.assertIn("Library.value", diagnostic["message"])
            self.assertEqual(diagnostic["position"]["column"], 1)

    def test_module_graph_discovery(self):
        with tempfile.TemporaryDirectory(prefix="fibril graph ") as directory:
            base = Path(directory)
            root = base / "source '🌍'"
            root.mkdir()
            def module(name, imports=(), body=""):
                path = root.joinpath(*name.split(".")).with_suffix(".fib")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("module " + name + "\n" +
                                "".join("import " + value + "\n" for value in imports) + body,
                                encoding="utf-8")
                return path
            shared = module("Shared", body='value : String\nvalue = "🌍"\n')
            module("Left", ("Shared",))
            module("Right", ("Shared",))
            entry = module("Main", ("Left", "Right"),
                           'main : IO Unit\nmain = putStrLn "must not execute"\n')
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            graph = json.loads(result.stdout)
            self.assertFalse(graph["checked"])
            self.assertEqual(graph["root"], str(root.resolve()))
            self.assertEqual([n["module"] for n in graph["modules"]], ["Shared", "Left", "Right", "Main"])
            self.assertEqual(graph["modules"][0]["bytes"], len(shared.read_bytes()))
            self.assertNotIn("must not execute", result.stdout)
            self.assertEqual(result.stderr, "")
            # No kernel admission: syntactically valid, ill-typed modules can be inspected.
            module("Shared", body="value : Bool\nvalue = missing\n")
            self.assertEqual(run("module-graph", str(root), str(entry)).returncode, 0)
            module("Shared", ("Main",))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Import cycle", result.stderr)
            module("Shared")
            module("Main", ("Absent",))
            result = run("module-graph", str(root), str(entry))
            self.assertIn(f"{entry.resolve()}:2:1:", result.stderr)
            self.assertIn("exact-case", result.stderr)
            self.assertEqual(result.stdout, "")
            module("Main", ("Wrong",))
            wrong = module("Wrong")
            wrong.write_text("module Different\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertIn(str(wrong.resolve()), result.stderr)
            self.assertIn("does not match", result.stderr)
            wrong.write_text("value : Bool\nvalue = True\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertIn("require a module header", result.stderr)
            # Canonical aliases must not claim a second logical module name.
            wrong.unlink()
            wrong.symlink_to(shared)
            module("Main", ("Shared", "Wrong"))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("does not match", result.stderr)
            # Check case using directory entries, even on case-insensitive filesystems.
            case = module("Case")
            case.rename(root / "case.fib")
            module("Main", ("Case",))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("exact-case", result.stderr)
            outside = base / "outside.fib"
            outside.write_text("module Escape\n", encoding="utf-8")
            (root / "Escape.fib").symlink_to(outside)
            module("Main", ("Escape",))
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("escapes canonical source root", result.stderr)
            self.assertEqual(result.stdout, "")
            result = run("module-graph", str(root), str(outside))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Entry escapes", result.stderr)
            # Named entries must map back to their canonical file.
            entry.write_text("module Unrelated\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            # Anonymous legacy entries remain inspectable, but not importable.
            entry.write_text("True\n", encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIsNone(json.loads(result.stdout)["modules"][0]["module"])

    def test_module_graph_budgets(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = root / "Main.fib"
            for count, accepted in ((31, True), (32, False)):
                for index in range(count):
                    (root / f"M{index}.fib").write_text(f"module M{index}\n", encoding="utf-8")
                entry.write_text("module Main\n" +
                                 "".join(f"import M{i}\n" for i in range(count)), encoding="utf-8")
                result = run("module-graph", str(root), str(entry))
                self.assertEqual(result.returncode == 0, accepted, result.stdout + result.stderr)
                if not accepted:
                    self.assertEqual(result.stdout, "")
                    self.assertIn("count budget", result.stderr)
            entry.write_text("module Main\n" + "".join(f"import M{i}\n" for i in range(9)), encoding="utf-8")
            for index in range(9):
                header = f"module M{index}\n--"
                (root / f"M{index}.fib").write_text(header + "a" * (65536 - len(header)), encoding="utf-8")
            result = run("module-graph", str(root), str(entry))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Aggregate", result.stderr)
            self.assertEqual(result.stdout, "")

    def test_module_document_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "metadata.fib"
            source = ("-- 🌍\r\nmodule Text.Greeting\r\nimport Data.String\r\n"
                      "hidden : String\r\nhidden = \"data\"\r\n"
                      "export\r\nvalue : String\r\nvalue = hidden\r\n")
            path.write_bytes(source.encode("utf-8"))
            result = run("symbols", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            symbols = json.loads(result.stdout)["symbols"]
            self.assertEqual([s["name"] for s in symbols], ["hidden", "value"])
            self.assertEqual([s["exported"] for s in symbols], [False, True])
            self.assertEqual(symbols[1]["range"]["start"]["line"], 6)
            self.assertEqual(symbols[1]["selection"]["start"]["line"], 7)
            for symbol in symbols:
                span = symbol["selection"]
                self.assertEqual(source[span["start"]["offset"]:span["end"]["offset"]], symbol["name"])
            result = run("definition", "8", "9", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            target = json.loads(result.stdout)["definition"]
            self.assertEqual(target["start"]["line"], 5)
            result = run("rename-preview", "8", "9", "renamed", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("project-aware", result.stderr)
            for args in (("check",), ("eval",), ("run",)):
                result = run(*args, str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Module checking requires --source-dir", result.stdout + result.stderr)
            result = run("check", "--json", str(path))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["position"]["line"], 2)
            for source in (
                "module A\nimport B\nimport B\n",
                "module A\nmodule B\n",
                "module A\nimport b\n",
                "module A\nvalue : Bool\nvalue = True\nimport B\n",
                "module A\nexport value : Bool\nvalue = True\n",
                "export\nmain : Bool\nmain = True\n",
                "module A\nexport\n",
            ):
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("symbols", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")

    def test_json_check_reports(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "checking.fib"
            for source in ("True", 'main : IO Unit\nmain = putStrLn "never printed"\n'):
                path.write_text(source, encoding="utf-8")
                result = run("check", "--json", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                report = json.loads(result.stdout)
                self.assertEqual(report["version"], 1)
                self.assertTrue(report["accepted"])
                self.assertEqual(report["diagnostics"], [])
                self.assertTrue(report["report"])
                self.assertNotIn("never printed", result.stdout)
                self.assertEqual(result.stderr, "")
            for source, stage, located in (
                ("missing", "resolution", True),
                ("\\(1 x : Bool) =>", "parsing", True),
                ("@", "lexing", True),
                ("(True : String)", "runtime-checking", False),
                ('(\\(1 x : String) => "discard") "input"', "runtime-checking", False),
            ):
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("check", "--json", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stderr, "")
                    report = json.loads(result.stdout)
                    self.assertFalse(report["accepted"])
                    self.assertEqual(report["report"], [])
                    diagnostic = report["diagnostics"][0]
                    self.assertEqual(diagnostic["stage"], stage)
                    self.assertEqual(diagnostic["severity"], "error")
                    self.assertEqual(diagnostic["position"] is not None, located)
                    self.assertIsNone(diagnostic["byteOffset"])
            source = '-- 🌍\r\nmain : String\r\nmain = missing\r\n'
            path.write_bytes(source.encode("utf-8"))
            result = run("check", "--json", str(path))
            point = json.loads(result.stdout)["diagnostics"][0]["position"]
            self.assertEqual(point, {"offset": source.index("missing"), "line": 3, "column": 8})
            for raw, byte_offset in ((b"\xff", 0), ("🌍".encode("utf-8") + b"\xff", 4)):
                path.write_bytes(raw)
                result = run("check", "--json", str(path))
                diagnostic = json.loads(result.stdout)["diagnostics"][0]
                self.assertEqual(diagnostic["stage"], "decoding")
                self.assertIsNone(diagnostic["position"])
                self.assertEqual(diagnostic["byteOffset"], byte_offset)
            path.write_text('"🌍"\n\u202e', encoding="utf-8")
            result = run("check", "--json", str(path))
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "source-validation")
            self.assertEqual(diagnostic["position"], {"offset": 4, "line": 2, "column": 1})
            self.assertIsNone(diagnostic["byteOffset"])
            path.unlink()
            result = run("check", "--json", str(path))
            self.assertNotEqual(result.returncode, 0)
            diagnostic = json.loads(result.stdout)["diagnostics"][0]
            self.assertEqual(diagnostic["stage"], "loading")
            self.assertIsNone(diagnostic["position"])
            self.assertEqual(result.stderr, "")

    def test_boolean_library(self):
        result = run("run", "examples/core/boolean-library.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Allowed.\nDenied.\nFallback enabled.\n")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "boolean-library.fib"
            for left in (False, True):
                expression = "notBool " + str(left)
                path.write_text("main : Bool\nmain = " + expression + "\n", encoding="utf-8")
                result = run("eval", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("Normal: " + str(not left), result.stdout)
                for right in (False, True):
                    for operation, expected in (("andBool", left and right), ("orBool", left or right)):
                        expression = f"{operation} {left} {right}"
                        path.write_text("main : Bool\nmain = " + expression + "\n", encoding="utf-8")
                        result = run("eval", str(path))
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        self.assertIn("Normal: " + str(expected), result.stdout)
            path.write_text(
                'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
                '  if andBool False () then putStrLn "yes" else putStrLn "no"\n',
                encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_pure_string_equality(self):
        result = run("run", "examples/core/string-equal.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\nHello, guest!\n")
        result = run("check", "examples/core/string-equal.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, Fibril!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "equal.fib"
            for expression, expected in (
                ('equalString "" ""', "True"),
                ('equalString "λ 🌍" "λ 🌍"', "True"),
                ('equalString "é" "é"', "False"),
                ('equalString "Fibril" "fibril"', "False"),
            ):
                path.write_text("main : Bool\nmain = " + expression + "\n", encoding="utf-8")
                result = run("eval", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("Normal: " + expected, result.stdout)
            path.write_text(
                'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
                '  if (\\(1 x : String) => equalString x x) "same" then putStrLn "yes" else putStrLn "no"\n',
                encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_pure_string_append(self):
        result = run("run", "examples/core/string-append.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, Fibril!\n")
        result = run("check", "examples/core/string-append.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, Fibril!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "append.fib"
            path.write_text('main : String\nmain = appendString "λ " "🌍"\n', encoding="utf-8")
            result = run("eval", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: "\\955 \\127757"', result.stdout)
            result = run("eval", "--fuel", "0", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn("Normal:", result.stdout)
            for expression in ('appendString True "bad"',
                               r'(\(1 x : String) => appendString x x) "twice"',
                               r'(\(0 x : String) => appendString x "suffix") "erased"'):
                path.write_text('main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
                                '  putStrLn (' + expression + ')\n', encoding="utf-8")
                result = run("run", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")

    def test_rename_preview(self):
        # ^ marks exactly the sites that may be edited; @ marks the query.
        accepted = [
            ('\\(1 ^x : Bool) => @^x', "flag"),
            ('let (^x : String) = "x 🌍" in (\\(first : String) => \\(1 second : String) => second) ^x @^x', "message"),
            ('let (1 y : String) = "outer" in let (1 ^x : String) = y in @^x', "y"),
            ('let (1 ^veryLongName : String) = "🌍" in @^veryLongName', "x"),
            ('^helper : Bool\n^helper = True\nmain : Bool\nmain = @^helper\n', "renamed"),
            ('main : IO Unit\nmain = do\n  (1 ^text : String) <- pure String "x"\n  putStrLn @^text\n', "message"),
            ('main : IO Unit\nmain = do\n  let (^text : String) = "x"\n  putStrLn ^text\n  putStrLn @^text\n', "value"),
            ('f : (0 A : Type 0) -> IO A\nf = \\(0 ^A : Type 0) => do (@^A)\n  let (A : Bool) = True\n  pure Unit ()\n', "Result"),
            ('-- λ 🌍\r\nlet (1 ^text : String) = "🌍" in @^text -- text\r\n', "renamed"),
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "rename.fib"
            for marked, replacement in accepted:
                with self.subTest(source=marked, replacement=replacement):
                    chars, sites, cursor = [], [], None
                    for char in marked:
                        if char == "^":
                            sites.append(len(chars))
                        elif char == "@":
                            cursor = len(chars)
                        else:
                            chars.append(char)
                    source = "".join(chars)
                    raw = source.encode("utf-8")
                    path.write_bytes(raw)
                    line = source[:cursor].count("\n") + 1
                    column = cursor - source.rfind("\n", 0, cursor)
                    result = run("rename-preview", str(line), str(column), replacement, str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    edits = json.loads(result.stdout)["edits"]
                    self.assertEqual([edit["range"]["start"]["offset"] for edit in edits], sites)
                    changed = source
                    for edit in reversed(edits):
                        span = edit["range"]
                        changed = changed[:span["start"]["offset"]] + edit["newText"] + changed[span["end"]["offset"]:]
                    self.assertEqual(path.read_bytes(), raw, "preview must not write source")
                    path.write_bytes(changed.encode("utf-8"))
                    result = run("symbols", str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            rejected = [
                ('let (x : Bool) = True in let (y : Bool) = False in x', 1, 6, "y"),
                ('let (y : Bool) = True in let (x : Bool) = False in y', 1, 31, "y"),
                ('let (x : String) = "x" in putStrLn x', 1, 6, "putStrLn"),
                ('let (x : Bool) = True in unknown x', 1, 6, "unknown"),
                ('helper : Bool\nhelper = True\nother : Bool\nother = helper', 1, 1, "other"),
                ('main : Bool\nmain = True', 1, 1, "entry"),
                ('helper : Bool\nhelper = True', 1, 1, "main"),
                ('missing', 1, 1, "value"),
            ]
            for source, line, column, replacement in rejected:
                with self.subTest(source=source, replacement=replacement):
                    path.write_text(source, encoding="utf-8")
                    before = path.read_bytes()
                    result = run("rename-preview", str(line), str(column), replacement, str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertEqual(path.read_bytes(), before)
                    if source.startswith("let") or replacement == "other":
                        self.assertIn("lexical resolution", result.stderr)
            source = "\\(1 x : Bool) => x"
            path.write_text(source, encoding="utf-8")
            for replacement in ("", "_", "Bool", "let", "bad name", "λ", "x" * 257):
                result = run("rename-preview", "1", "5", replacement, str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
            result = run("rename-preview", "1", "5", "x", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(json.loads(result.stdout)["edits"], [])
            # Enforce UTF-8 bytes, not scalar counts, on the proposed result.
            prefix = 'let (1 x : String) = "🌍" in x --'
            for size, succeeds in ((65534, True), (65535, False)):
                source = prefix + "a" * (size - len(prefix.encode("utf-8")))
                path.write_bytes(source.encode("utf-8"))
                result = run("rename-preview", "1", "8", "xx", str(path))
                self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)
                self.assertEqual(path.stat().st_size, size)

    def test_same_file_lexical_references(self):
        # ^ marks every expected site; @ marks the query point.
        fixtures = [
            '^first : Bool\n^first = True\nmain : Bool\nmain = @^first\n',
            'let (1 ^text : String) = "outer" in let (1 text : String) = @^text in text',
            'let (1 text : String) = "outer" in let (1 ^text : String) = text in @^text',
            'main : IO Unit\nmain = do\n  let (text : String) = "old"\n  (1 ^text : String) <- pure String text\n  putStrLn @^text\n',
            'main : IO Unit\nmain = do\n  let (1 ^text : String) = "old"\n  (1 text : String) <- pure String @^text\n  putStrLn text\n',
            'f : (0 A : Type 0) -> IO A\nf = \\(0 ^A : Type 0) => do (@^A)\n  (1 A : Bool) <- pure Bool True\n  if A then pure Unit () else pure Unit ()\n',
            '-- 🌍\r\n^item : String\r\n^item = "item"\r\nmain : String\r\nmain = (@^item) -- item\r\n',
            'let (1 ^text : String) = "text 🌍" in @^text -- text',
            '@putStrLn "prelude"',
            'main : Bool\nmain = @later\nlater : Bool\nlater = True\n',
            '\\(1 _ : String) => @_',
            'let (1 text : String) = "x" in "literal @text"',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "references.fib"
            for marked in fixtures:
                with self.subTest(source=marked):
                    chars, sites, cursor = [], [], None
                    for char in marked:
                        if char == "^":
                            sites.append(len(chars))
                        elif char == "@":
                            cursor = len(chars)
                        else:
                            chars.append(char)
                    source = "".join(chars)
                    path.write_bytes(source.encode("utf-8"))
                    line = source[:cursor].count("\n") + 1
                    column = cursor - source.rfind("\n", 0, cursor)
                    result = run("references", str(line), str(column), str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stderr, "")
                    payload = json.loads(result.stdout)
                    self.assertEqual(payload["version"], 1)
                    actual = [span["start"]["offset"] for span in payload["references"]]
                    self.assertEqual(actual, sites)
                    self.assertEqual(actual, sorted(set(actual)))
                    for span in payload["references"]:
                        token = source[span["start"]["offset"]:span["end"]["offset"]]
                        self.assertTrue(token.isidentifier())
            path.write_text("first : Bool\nfirst = True\nlater : Bool", encoding="utf-8")
            result = run("references", "1", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Parsing", result.stderr)
            result = run("references", "0", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_same_file_lexical_definition(self):
        # Mark cursor with @ and expected target with ^; neither reaches the parser.
        fixtures = [
            '@first : Bool\n^first = True\n',
            'first : Bool\n^first = True\nmain : Bool\nmain = @first\n',
            '(\\(1 ^value : String) => @value) "x"',
            'let (1 text : String) = "outer" in let (1 ^text : String) = "inner" in @text',
            'let (1 ^text : String) = "outer" in let (1 text : String) = @text in text',
            'main : IO Unit\nmain = do\n  (1 ^message : String) <- pure String "x"\n  putStrLn @message\n',
            'main : IO Unit\nmain = do\n  let (1 ^message : String) = "outer"\n  (1 message : String) <- pure String @message\n  putStrLn message\n',
            'f : (0 A : Type 0) -> IO A\nf = \\(0 ^A : Type 0) => do (@A)\n  let (A : Bool) = True\n  pure Unit ()\n',
            'f : (0 A : Type 0) -> IO A\nf = \\(0 A : Type 0) => do (A)\n  (1 ^A : Bool) <- pure Bool True\n  if @A then pure Unit () else pure Unit ()\n',
            '-- λ 🌍\r\n0 item : String\r\n^item = "🌍"\r\nmain : String\r\nmain = (@item)\r\n',
            'let (0 ignored : String) = "🌍" in let (1 ^text : String) = "x" in @text',
            '(0 ^A : Type 0) -> (1 value : @A) -> A',
            '\\(0 ^A : Type 0) => \\(1 A : @A) => A',
            'first : Bool\n^first = True\nmain : Bool\nmain =\n\t@first\n',
            # Unknown, forward, recursive, wildcard, comment/string, punctuation misses.
            '@putStrLn "external"',
            'main : Bool\nmain = @later\nlater : Bool\nlater = True\n',
            'recursive : Bool\nrecursive = @recursive\n',
            '\\(1 _ : String) => @_',
            'let (1 text : String) = "x" in "literal @text"',
            'let (1 text : String) = "x" in text -- @text',
            'let (1 text : String) = "x" in @(text)',
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "navigation.fib"
            for marked in fixtures:
                with self.subTest(source=marked):
                    chars, cursor, target = [], None, None
                    for char in marked:
                        if char == "@":
                            cursor = len(chars)
                        elif char == "^":
                            target = len(chars)
                        else:
                            chars.append(char)
                    source = "".join(chars)
                    path.write_bytes(source.encode("utf-8"))
                    line = source[:cursor].count("\n") + 1
                    column = cursor - source.rfind("\n", 0, cursor)
                    result = run("definition", str(line), str(column), str(path))
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(result.stderr, "")
                    payload = json.loads(result.stdout)
                    self.assertEqual(payload["version"], 1)
                    if target is None:
                        self.assertIsNone(payload["definition"])
                    else:
                        self.assertEqual(payload["definition"]["start"]["offset"], target)
            for text in ("0", "-1", "65538", "abc", "999999999999"):
                result = run("definition", text, "1", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn("Coordinates", result.stderr)
            path.write_text("first : Bool\nfirst = True\nlater : Bool", encoding="utf-8")
            result = run("definition", "2", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("Parsing", result.stderr)
            path.unlink()
            result = run("definition", "1", "1", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_document_symbols(self):
        result = run("symbols", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["version"], 1)
        self.assertEqual([s["name"] for s in payload["symbols"]], ["finished", "main"])
        self.assertEqual(result.stderr, "")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "symbols.fib"
            source = '-- λ 🌍\r\n0 item : String\r\nitem = "🌍"\r\n\r\nhelper : Missing\r\nhelper = unknown\r\n'
            path.write_bytes(source.encode("utf-8"))
            result = run("symbols", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            symbols = json.loads(result.stdout)["symbols"]
            self.assertEqual([s["name"] for s in symbols], ["item", "helper"])
            self.assertEqual(symbols[0]["quantity"], "0")
            self.assertEqual(symbols[0]["selection"]["start"]["column"], 3)
            for symbol in symbols:
                for field in ("selection", "definitionSelection"):
                    span = symbol[field]
                    self.assertEqual(source[span["start"]["offset"]:span["end"]["offset"]],
                                     symbol["name"])
                self.assertLessEqual(symbol["range"]["start"]["offset"],
                                     symbol["selection"]["start"]["offset"])
                self.assertGreaterEqual(symbol["range"]["end"]["offset"],
                                        symbol["definitionSelection"]["end"]["offset"])
            for source in ("", "-- comment\n", "True"):
                path.write_text(source, encoding="utf-8")
                result = run("symbols", str(path))
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(json.loads(result.stdout)["symbols"], [])
            for source in ("first : Bool\nfirst = True\nlater : Bool",
                           "name : Bool\nwrong = True", "\u202e"):
                path.write_text(source, encoding="utf-8")
                result = run("symbols", str(path))
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(str(path), result.stderr)
            path.unlink()
            result = run("symbols", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(path), result.stderr)

    def test_annotated_do_results(self):
        result = run("run", "examples/core/do-result.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "Preparing a String result.\n"
                         "Typed do blocks can return values.\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/do-result.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        result = run("eval", "examples/core/do-result.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal:", result.stdout)
        self.assertNotIn("\nPreparing a String result.\n", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "result.fib"
            path.write_text(
                'main : IO Unit\nmain = do (Unit)\n'
                '  putStrLn "must not print"\n'
                '  (1 text : String) <- pure String "wrong result"\n'
                '  pure String text\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            path.write_text('main : IO String\nmain = do (String)\n'
                            '  pure String "returned"\n', encoding="utf-8")
            result = run("eval", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('Normal: (Pure "returned")', result.stdout)
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")

    def test_do_let_statements(self):
        result = run("run", "examples/core/do-let.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "Pure computations belong in do blocks too.\n" +
                         "An unrestricted binding can be reused.\n" * 2)
        result = run("check", "examples/core/do-let.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "let.fib"
            prefix = 'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
            for tail in (
                '  let (1 text : String) = "unused"\n  pure Unit ()\n',
                '  let (1 text : String) = "twice"\n  putStrLn text\n  putStrLn text\n',
                '  let (0 text : String) = "erased"\n  putStrLn text\n',
                '  let (text : String) = True\n  putStrLn text\n',
                '  let (text : String) = "last"\n',
            ):
                with self.subTest(tail=tail):
                    path.write_text(prefix + tail, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
            path.write_text(prefix + '  let (1 text : String) = missing\n'
                            '  putStrLn text\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.stdout, "")
            self.assertIn(f"{path}:4:27: Resolution:", result.stderr)

    def test_typed_do_bindings(self):
        result = run("run", "examples/core/do-bindings.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "A named Fibril IO result.\n"
                         "The previous action completed.\n"
                         "Typed do bindings work.\n")
        result = run("check", "examples/core/do-bindings.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        result = run("eval", "examples/core/do-bindings.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal:", result.stdout)
        self.assertNotIn("\nTyped do bindings work.\n", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "binding.fib"
            prefix = 'main : IO Unit\nmain = do\n  putStrLn "must not print"\n'
            for tail in (
                '  (1 text : String) <- pure Bool True\n  putStrLn text\n',
                '  (1 text : String) <- pure String "unused"\n  pure Unit ()\n',
                '  (1 text : String) <- pure String "twice"\n'
                '  putStrLn text\n  putStrLn text\n',
                '  (1 text : String) <- pure String text\n  putStrLn text\n',
                '  (1 text : String) <- pure String "last"\n',
            ):
                with self.subTest(tail=tail):
                    path.write_text(prefix + tail, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.write_text(prefix + '  (1 text : String) <- pure String missing\n'
                            '  putStrLn text\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.stdout, "")
            self.assertIn(f"{path}:4:36: Resolution:", result.stderr)

    def test_io_map_is_a_checked_library_function(self):
        result = run("check", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: (IO Unit)", result.stdout)
        self.assertNotIn("Mapped result received.", result.stdout)
        result = run("run", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout,
                         "The first action runs before its result is mapped.\n"
                         "Mapped result received.\n")
        self.assertEqual(result.stderr, "")
        result = run("eval", "examples/core/io-map.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal:", result.stdout)
        self.assertNotIn("\nMapped result received.\n", result.stdout)

    def test_expanded_io_plan_limit_has_no_output_prefix(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "expanded.fib"
            path.write_text(
                'twice : IO Unit\ntwice = do\n'
                '  putStrLn "never"\n  putStrLn "never"\n'
                'main : IO Unit\nmain = do\n' + '  twice\n' * 33,
                encoding="utf-8")
            result = run("check", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn("output action count limit", result.stderr)

    def test_console_do_sequence(self):
        result = run("run", "examples/core/console-sequence.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, world!\nFibril can sequence console output.\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/console-sequence.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, world!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sequence.fib"
            prefix = 'main : IO Unit\nmain = do\n  putStrLn "first"\n'
            invalid = [
                prefix + '  unknown "must not print"\n',
                prefix + '   putStrLn "bad indent"\n',
                prefix + 'putStrLn "dedented"\n',
                prefix + '  putStrLn "bad\\q"\n',
                prefix + '  putStrLn "ok" ()\n',
                'main : IO Unit\nmain = do\n',
                'main : IO Unit\nmain = do\n' + '  putStrLn "quota"\n' * 65,
            ]
            for source in invalid:
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.write_text('main : IO Unit\nmain = do\n' + '  putStrLn "quota"\n' * 64,
                            encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, "quota\n" * 64)

    def test_hello_world_runner(self):
        result = run("run", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "Hello, world!\n")
        self.assertEqual(result.stderr, "")
        result = run("check", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Runtime checking: accepted", result.stdout)
        self.assertNotIn("Hello, world!", result.stdout)
        result = run("eval", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Normal: (WriteLine "Hello, world!")', result.stdout)
        self.assertNotIn("\nHello, world!\n", result.stdout)
        result = run("check", "--erased", "examples/core/hello-world.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("Hello, world!", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "hello.fib"
            path.write_text('main : IO Unit\nmain =\n  putStrLn "λ 🌍\\nquote: \\" slash: \\\\ tab:\\t"\n', encoding="utf-8")
            result = run("run", str(path))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(result.stdout, 'λ 🌍\nquote: " slash: \\ tab:\t\n')
            bad_sources = [
                'main : IO Unit\nmain = putStrLn "must not print"\nmain = putStrLn "extra"',
                'main : IO Unit\nmain = putStrLn "must not print" ()',
                'main : IO Unit\nmain = putStrLn "unterminated',
                'main : IO Unit\nmain = putStrLn "bad\\q"',
                'main : IO Unit\nmain = unknown "must not print"',
                'main : IO Bool\nmain = putStrLn "must not print"',
                'main : Bool\nmain = True',
                'main : IO Unit\nmain = putStrLn "raw\nnewline"',
            ]
            for source in bad_sources:
                with self.subTest(source=source):
                    path.write_text(source, encoding="utf-8")
                    result = run("run", str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(str(path), result.stderr)
            path.unlink()
            result = run("run", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, "")
            self.assertIn(str(path), result.stderr)

    def test_declaration_files(self):
        result = run("eval", "--fuel", "4", "examples/core/declarations.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: Bool", result.stdout)
        self.assertIn("Normal: True", result.stdout)
        result = run("check", "examples/core/declarations.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "program.fib"
            path.write_text("main : Bool\nmain = other\n", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:2:8: Resolution:", result.stdout)
            path.write_text("main : Bool\nwrong = True\n", encoding="utf-8")
            result = run("eval", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:2:1: Parsing:", result.stdout)
            self.assertIn("Expected definition of", result.stdout)

    def test_type_mismatch_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "types.fib"
            cases = [
                ("(True : Unit)", "inferred: Bool; expected: Unit"),
                ("if True then True else ()", "then: Bool; else: Unit"),
                ("() ()", "found: Unit"),
                (r"\(1 x : ()) => x", "Expected a universe; found: Unit"),
            ]
            for source, expected in cases:
                path.write_text(source, encoding="utf-8")
                for command in ("check", "eval"):
                    with self.subTest(source=source, command=command):
                        result = run(command, str(path))
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn(expected, result.stdout)
                        self.assertIn(f"{path}: Runtime checking:", result.stdout)
                        self.assertNotIn("^", result.stdout)
            path.write_text("(Type 0 : Type 0)", encoding="utf-8")
            result = run("check", "--erased", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("inferred: Type1; expected: Type0", result.stdout)

    def test_located_source_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.fib"
            path.write_bytes(b"-- comment\r\n\tmissing")
            for command in ("check", "eval"):
                with self.subTest(command=command):
                    result = run(command, str(path))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn(f"{path}:2:2: Resolution:", result.stdout)
                    self.assertIn("  2 |  missing", result.stdout)
                    self.assertIn("    |  ^", result.stdout)
            path.write_text("if True then ()", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:1:16: Parsing:", result.stdout)
            self.assertIn("Expected else", result.stdout)
            self.assertIn("^", result.stdout)
            path.write_text("@", encoding="utf-8")
            result = run("lex-source", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}:1:1: Lexing:", result.stdout)
            self.assertIn("  1 | @", result.stdout)
            path.write_text("Bool", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(f"{path}: Runtime checking:", result.stdout)
            self.assertNotIn("^", result.stdout)

    def test_boolean_program(self):
        result = run("eval", "examples/core/boolean.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: Bool", result.stdout)
        self.assertIn("Normal: True", result.stdout)
        result = run("eval", "--fuel", "2", "examples/core/branch-permissions.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("(If v1 () v0)", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "branches.fib"
            path.write_text(r"\(1 x : Unit) => if True then x else ()", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Binder usage", result.stdout)

    def test_unit_elimination(self):
        result = run("eval", "--fuel", "2", "examples/core/consume-unit.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal: ()", result.stdout)
        result = run("eval", "--fuel", "1", "examples/core/consume-unit.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("budget exhausted", result.stdout)
        self.assertNotIn("Normal:", result.stdout)

    def test_unit_value_program(self):
        result = run("eval", "examples/core/unit.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Type: Unit", result.stdout)
        self.assertIn("Normal: ()", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "discard.fib"
            path.write_text(r"\(1 x : Unit) => ()", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Binder usage", result.stdout)

    def test_typed_local_binding(self):
        result = run("check", "examples/core/local-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        result = run("eval", "examples/core/local-identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Normal: (Lam 1 Type0 v0)", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "recursive.fib"
            path.write_text("let (1 x : Type 0) = x in x", encoding="utf-8")
            result = run("check", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Unbound name", result.stdout)

    def test_source_ascription(self):
        result = run("check", "examples/core/identity-annotated.fib")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("(Pi 0 Type0 (Pi 1 v0 v1))", result.stdout)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ascription.fib"
            path.write_text("(Type 0 : Type 0)", encoding="utf-8")
            result = run("check", "--erased", str(path))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("not compatible", result.stdout)

    def test_checked_reference_evaluation(self):
        path = "examples/core/evaluate-identity.fib"
        result = run("eval", path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("not compiled execution", result.stdout)
        self.assertIn("Normal: (Lam 1 Type0 v0)", result.stdout)
        result = run("eval", "--fuel", "0", path)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("budget exhausted", result.stdout)
        self.assertNotIn("Normal:", result.stdout)
        result = run("eval", "--fuel", "0", "examples/core/identity.fib")
        self.assertEqual(result.returncode, 0, result.stdout)
        for value in ("-1", "4097", "99999999999", "wrong"):
            with self.subTest(fuel=value):
                result = run("eval", "--fuel", value, path)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Fuel must", result.stdout)
        result = run("eval", "examples/core/identity-type.fib")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Runtime", result.stdout)

    def test_unsupported_commands_fail(self):
        for args in (("build", "example.fib"), ("demo", "extra"), ("--unknown",)):
            with self.subTest(args=args):
                result = run(*args)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Unsupported command", result.stdout)


if __name__ == "__main__":
    unittest.main()
