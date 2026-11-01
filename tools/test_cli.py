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
