#!/usr/bin/env python3
"""Protocol, unsaved-buffer, compiler and workspace integration regressions."""
import io
import json
import os
from pathlib import Path
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import unittest

from fibril_lsp import LSPError, Positions, changed_text, read_frame, uri_path

ROOT = Path(__file__).resolve().parents[1]
SERVER = ROOT / "tools/fibril_lsp.py"
BINARY = ROOT / "build/exec/fibril"
SOURCE = 'greet : (1 name : String) -> String\ngreet = \\(1 name : String) => name\nmain : IO Unit\nmain = putStrLn (appendString "🌍 " (greet "world"))\n'


class Client:
    def __init__(self, root, binary=BINARY, options=None, timeout=15):
        self.process = subprocess.Popen([sys.executable, str(SERVER), "--fibril", str(binary), "--timeout", str(timeout)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.queue, self.saved, self.ident = queue.Queue(), [], 0
        def reader():
            try:
                while True:
                    frame = read_frame(self.process.stdout)
                    if frame is None:
                        break
                    self.queue.put(json.loads(frame))
            except Exception as error:
                self.queue.put(error)
        self.reader = threading.Thread(target=reader, daemon=True)
        self.reader.start()
        self.capabilities = self.request("initialize", {"rootUri": root.as_uri(), "capabilities": {
            "workspace": {"workspaceEdit": {"documentChanges": True}}}, "initializationOptions": options or {}})["result"]["capabilities"]
        self.notify("initialized", {})

    def send(self, packet):
        body = json.dumps({"jsonrpc": "2.0", **packet}, ensure_ascii=False).encode()
        self.process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
        self.process.stdin.flush()

    def notify(self, method, params):
        self.send({"method": method, "params": params})

    def begin(self, method, params):
        self.ident += 1
        self.send({"id": self.ident, "method": method, "params": params})
        return self.ident

    def receive(self, predicate, timeout=25):
        for index, value in enumerate(self.saved):
            if predicate(value):
                return self.saved.pop(index)
        deadline = time.monotonic() + timeout
        while True:
            value = self.queue.get(timeout=max(0.01, deadline - time.monotonic()))
            if isinstance(value, Exception):
                raise value
            if predicate(value):
                return value
            self.saved.append(value)

    def response(self, ident):
        return self.receive(lambda value: value.get("id") == ident)

    def request(self, method, params):
        return self.response(self.begin(method, params))

    def open(self, path, text, version=1):
        self.notify("textDocument/didOpen", {"textDocument": {"uri": path.as_uri(), "languageId": "fibril", "version": version, "text": text}})

    def change(self, path, text, version):
        self.notify("textDocument/didChange", {"textDocument": {"uri": path.as_uri(), "version": version}, "contentChanges": [{"text": text}]})

    def diagnostics(self, path, version=None, errors=None):
        def matches(value):
            params = value.get("params", {})
            return (value.get("method") == "textDocument/publishDiagnostics" and params.get("uri") == path.as_uri() and
                (version is None or params.get("version") == version) and
                (errors is None or bool(params["diagnostics"]) == errors))
        result = self.receive(matches)["params"]
        self.saved = [value for value in self.saved if not (value.get("method") == "textDocument/publishDiagnostics" and value.get("params", {}).get("uri") == path.as_uri())]
        return result

    def close(self):
        if self.process.poll() is None:
            try:
                response = self.request("shutdown", {})
                if response.get("result", "missing") is not None:
                    raise AssertionError(response)
                self.notify("exit", {})
                self.process.stdin.close()
                self.process.wait(timeout=10)
                if self.process.returncode != 0:
                    raise AssertionError(self.process.stderr.read().decode())
            finally:
                if self.process.poll() is None:
                    self.process.terminate()
                    self.process.wait(timeout=10)
        if not self.process.stdin.closed:
            self.process.stdin.close()
        self.reader.join(timeout=2)
        self.process.stdout.close()
        self.process.stderr.close()


class Coordinates(unittest.TestCase):
    def test_utf16_and_crlf_round_trip(self):
        text = "α🌍é\r\nnext\n"
        mapper = Positions(text)
        for offset in [0, 1, 2, 3, 4, 6, 7, len(text)]:
            self.assertEqual(mapper.offset(mapper.point(offset)), offset)
        self.assertEqual(mapper.location({"line": 0, "character": 3}), (1, 3))
        with self.assertRaises(LSPError):
            mapper.offset({"line": 0, "character": 2})
        with self.assertRaises(LSPError):
            mapper.offset({"line": 0, "character": 100})

    def test_ordered_incremental_changes(self):
        text = "a🌍b\r\nend"
        change = {"range": {"start": {"line": 0, "character": 1}, "end": {"line": 0, "character": 3}}, "rangeLength": 2, "text": "X"}
        self.assertEqual(changed_text(text, [change]), "aXb\r\nend")
        with self.assertRaises(LSPError):
            changed_text(text, [{**change, "rangeLength": 1}])
        with self.assertRaises(LSPError):
            changed_text(text, [{"text": "\ud800"}])

    def test_uri_validation(self):
        self.assertEqual(uri_path("file:///tmp/a%20%CE%BB.fib"), Path("/tmp/a λ.fib").resolve())
        for uri in ["https://host/a", "file://remote/a", "file:///tmp/a#part", "file:///tmp/%00", "file:///tmp/%ZZ"]:
            with self.subTest(uri=uri), self.assertRaises(LSPError):
                uri_path(uri)

    def test_framing_uses_bytes_and_rejects_ambiguous_headers(self):
        body = json.dumps({"text": "🌍"}, ensure_ascii=False).encode()
        self.assertEqual(read_frame(io.BytesIO(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)), body)
        for raw in [b"Content-Length: 1\n\nx", b"Content-Length: -1\r\n\r\n", b"Content-Length: 1\r\nContent-Length: 2\r\n\r\nx", b"Content-Length: 5\r\n\r\nx"]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                read_frame(io.BytesIO(raw))


@unittest.skipUnless(BINARY.exists(), "make -j8 build first")
class Integration(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fibril lsp 'λ' ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.path = self.root / "Buffer.fib"
        self.disk = 'main : IO Unit\nmain = putStrLn "disk"\n'
        self.path.write_text(self.disk, encoding="utf-8")

    def client(self, **kwargs):
        client = Client(self.root, **kwargs)
        self.addCleanup(client.close)
        return client

    def query(self, source=SOURCE, word="greet", last=True):
        index = source.rindex(word) if last else source.index(word)
        return {"textDocument": {"uri": self.path.as_uri()}, "position": Positions(source).point(index)}

    def test_lifecycle_capabilities_and_unknown_methods(self):
        client = self.client()
        self.assertEqual(client.capabilities["positionEncoding"], "utf-16")
        self.assertEqual(client.capabilities["textDocumentSync"]["change"], 2)
        self.assertNotIn("completionProvider", client.capabilities)
        self.assertEqual(client.request("workspace/symbol", {})["error"]["code"], -32601)
        self.assertEqual(client.request("initialize", {})["error"]["code"], -32600)

    def test_shutdown_null_and_post_shutdown_requests(self):
        client = self.client()
        self.assertIsNone(client.request('shutdown', None)['result'])
        self.assertEqual(client.request('textDocument/documentSymbol', {})['error']['code'], -32600)
        client.notify('exit', None)
        client.process.wait(timeout=10)
        self.assertEqual(client.process.returncode, 0)

    def test_dirty_diagnostics_incremental_sync_and_close(self):
        client = self.client()
        bad = 'main : IO Unit\nmain = absent\n'
        client.open(self.path, bad, 7)
        diagnostic = client.diagnostics(self.path, 7, True)
        self.assertIn("absent", diagnostic["diagnostics"][0]["message"])
        client.notify("textDocument/didChange", {"textDocument": {"uri": self.path.as_uri(), "version": 8}, "contentChanges": [{
            "range": {"start": {"line": 1, "character": 7}, "end": {"line": 1, "character": 13}}, "text": 'putStrLn "fixed"'}]})
        self.assertEqual(client.diagnostics(self.path, 8, False)["diagnostics"], [])
        self.assertEqual(self.path.read_text(), self.disk)
        client.notify("textDocument/didClose", {"textDocument": {"uri": self.path.as_uri()}})
        self.assertEqual(client.diagnostics(self.path)["diagnostics"], [])

    def test_utf16_definition_references_symbols_and_rename(self):
        client = self.client()
        client.open(self.path, SOURCE, 3)
        self.assertEqual(client.diagnostics(self.path, 3, False)["diagnostics"], [])
        query = self.query()
        target = client.request("textDocument/definition", query)["result"]
        self.assertEqual(target["uri"], self.path.as_uri())
        span = target["range"]
        mapper = Positions(SOURCE)
        self.assertEqual(SOURCE[mapper.offset(span["start"]):mapper.offset(span["end"])], "greet")
        refs = client.request("textDocument/references", {**query, "context": {"includeDeclaration": False}})["result"]
        self.assertEqual(len(refs), 1, refs)
        self.assertEqual(refs[0]["range"]["start"], query["position"])
        symbols = client.request("textDocument/documentSymbol", {"textDocument": query["textDocument"]})["result"]
        self.assertEqual([symbol["name"] for symbol in symbols], ["greet", "main"])
        edit = client.request("textDocument/rename", {**query, "newName": "salute"})["result"]
        change = edit["documentChanges"][0]
        self.assertEqual(change["textDocument"]["version"], 3)
        self.assertEqual(len(change["edits"]), 3)
        self.assertEqual(self.path.read_text(), self.disk)

    def test_hover_formatting_and_invalid_positions(self):
        client = self.client()
        source = 'main   : IO Unit\nmain = putStrLn  "🌍"\n'
        client.open(self.path, source)
        client.diagnostics(self.path, 1, False)
        query = self.query(source, "String") if "String" in source else self.query(source, "IO")
        hover = client.request("textDocument/hover", query)["result"]
        self.assertIn("IO", hover["contents"]["value"])
        edits = client.request("textDocument/formatting", {"textDocument": query["textDocument"], "options": {"tabSize": 2, "insertSpaces": True}})["result"]
        self.assertTrue(edits)
        self.assertEqual(edits[0]["range"]["end"], {"line": 2, "character": 0})
        self.assertEqual(self.path.read_text(), self.disk)
        bad = {**query, "position": {"line": 1, "character": 999}}
        self.assertEqual(client.request("textDocument/definition", bad)["error"]["code"], -32602)

    def test_unsaved_imports_reexports_and_dependency_invalidation(self):
        root = self.root
        a = root / "A.fib"
        b = root / "B.fib"
        main = root / "Main.fib"
        good = 'module A\nexport\ngreeting : String\ngreeting = "hello"\n'
        a.write_text(good)
        b.write_text('module B\nimport public A (greeting)\n')
        text = 'module Main\nimport B as Public\nmain : IO Unit\nmain = putStrLn Public.greeting\n'
        main.write_text(text)
        client = self.client()
        client.open(main, text)
        client.diagnostics(main, 1, False)
        client.open(a, good)
        client.diagnostics(a, 1, False)
        result = client.request("textDocument/definition", {"textDocument": {"uri": main.as_uri()}, "position": Positions(text).point(text.index("greeting"))})["result"]
        self.assertEqual(result["uri"], a.as_uri())
        client.change(a, good.replace('String', 'Bool').replace('"hello"', 'True'), 2)
        self.assertTrue(client.diagnostics(main, 1, True)["diagnostics"])
        client.notify("textDocument/didClose", {"textDocument": {"uri": a.as_uri()}})
        self.assertEqual(client.diagnostics(main, 1, False)["diagnostics"], [])
        self.assertEqual(a.read_text(), good)

    def test_closed_dependency_disk_changes_trigger_rechecking(self):
        a = self.root / 'A.fib'
        good = 'module A\nexport\ngreeting : String\ngreeting = "hello"\n'
        a.write_text(good)
        text = 'module Buffer\nimport A\nmain : IO Unit\nmain = putStrLn A.greeting\n'
        self.path.write_text(text)
        client = self.client()
        client.open(self.path, text)
        client.diagnostics(self.path, 1, False)
        a.write_text(good.replace('String', 'Bool').replace('"hello"', 'True'))
        self.assertTrue(client.diagnostics(self.path, 1, True)['diagnostics'])
        a.write_text(good)
        self.assertEqual(client.diagnostics(self.path, 1, False)['diagnostics'], [])

    def test_packages_and_entry_free_library_json(self):
        library = self.root / "lib"
        app = self.root / "app"
        (library / "src/Lib").mkdir(parents=True)
        (app / "src").mkdir(parents=True)
        (library / "fibril.yaml").write_text('schema: 1\nname: lib\nmodule-prefix: Lib\nsource-dir: src\nfoundation: de-morgan\nmodules:\n  - Lib.Text\n')
        (app / "fibril.yaml").write_text('schema: 1\nname: app\nmodule-prefix: App\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  lib:\n    path: ../lib\n')
        lib = library / "src/Lib/Text.fib"
        lib_text = 'module Lib.Text\nexport\ngreeting : String\ngreeting = "hello"\n'
        lib.write_text(lib_text)
        main = app / "src/Main.fib"
        text = 'module Main\nimport Lib.Text\nmain : IO Unit\nmain = putStrLn Lib.Text.greeting\n'
        main.write_text(text)
        checked = subprocess.run([str(BINARY), 'check', '--json', '--package', str(library / 'fibril.yaml')], capture_output=True, timeout=20)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertTrue(json.loads(checked.stdout)['accepted'])
        client = self.client()
        client.open(main, text)
        client.diagnostics(main, 1, False)
        client.open(lib, lib_text)
        self.assertEqual(client.diagnostics(lib, 1, False)["diagnostics"], [])
        target = client.request("textDocument/definition", {"textDocument": {"uri": main.as_uri()}, "position": Positions(text).point(text.index("greeting"))})["result"]
        self.assertEqual(target["uri"], lib.as_uri())
        client.change(lib, lib_text.replace('String', 'Bool').replace('"hello"', 'True'), 2)
        self.assertTrue(client.diagnostics(main, 1, True)["diagnostics"])
        self.assertEqual(lib.read_text(), lib_text)

    def test_local_syntax_services_survive_invalid_project_metadata(self):
        (self.root / 'fibril.yaml').write_text('not a valid manifest\n')
        text = 'module Buffer\nmain   : IO Unit\nmain = putStrLn "hello"\n'
        client = self.client()
        client.open(self.path, text)
        client.diagnostics(self.path, 1, True)
        params = {"textDocument": {"uri": self.path.as_uri()}}
        self.assertEqual(client.request('textDocument/documentSymbol', params)['result'][0]['name'], 'main')
        self.assertTrue(client.request('textDocument/formatting', {**params, 'options': {}})['result'])
        self.assertEqual(self.path.read_text(), self.disk)

    def test_out_of_order_versions_leave_the_buffer_unchanged(self):
        client = self.client()
        client.open(self.path, SOURCE, 3)
        client.diagnostics(self.path, 3, False)
        client.change(self.path, 'broken', 2)
        log = client.receive(lambda value: value.get("method") == "window/logMessage")
        self.assertIn("monotonically", log["params"]["message"])
        result = client.request("textDocument/documentSymbol", {"textDocument": {"uri": self.path.as_uri()}})
        self.assertEqual([symbol["name"] for symbol in result["result"]], ["greet", "main"])

    def test_dependency_cannot_escape_workspace_snapshot(self):
        (self.root / 'fibril.yaml').write_text('schema: 1\nname: app\nmodule-prefix: App\nsource-dir: src\nfoundation: de-morgan\nentry: Main\ndependencies:\n  other:\n    path: ../outside\n')
        (self.root / 'src').mkdir()
        main = self.root / 'src/Main.fib'
        text = 'module Main\nmain : IO Unit\nmain = putStrLn "safe"\n'
        main.write_text(text)
        client = self.client()
        client.open(main, text)
        diagnostics = client.diagnostics(main, 1, True)["diagnostics"]
        self.assertIn("escapes workspace", diagnostics[0]["message"])

    def test_symlink_import_is_not_followed(self):
        with tempfile.TemporaryDirectory() as outside:
            secret = Path(outside) / 'Dependency.fib'
            secret.write_text('module Dependency\nexport\nsecret : String\nsecret = "DO_NOT_READ_OUTSIDE"\n')
            (self.root / 'Dependency.fib').symlink_to(secret)
            text = 'module Buffer\nimport Dependency\nmain : IO Unit\nmain = putStrLn Dependency.secret\n'
            self.path.write_text(text)
            client = self.client()
            client.open(self.path, text)
            diagnostics = client.diagnostics(self.path, 1, True)
            self.assertNotIn("DO_NOT_READ_OUTSIDE", json.dumps(diagnostics))

    def test_navigation_rejects_backend_path_outside_snapshot(self):
        script = self.root / 'bad-compiler'
        script.write_text('#!' + sys.executable + '\nimport json,sys\np={"version":2,"coordinates":"unicode-scalars;offset=0;line=1;column=1","accepted":True,"diagnostics":[],"sources":[]}\n'
            'if sys.argv[1]=="check":\n p["sources"]=[{"path":sys.argv[-1],"text":open(sys.argv[-1]).read()}]\n'
            'if sys.argv[1]=="definition":\n p.update(checked=True,query=sys.argv[-1],definition={"path":"/etc/passwd","range":{"start":{"offset":0},"end":{"offset":1}}})\n'
            'print(json.dumps(p))\n')
        script.chmod(0o755)
        text = 'module Buffer\nmain : IO Unit\nmain = putStrLn "safe"\n'
        client = self.client(binary=script)
        client.open(self.path, text)
        client.diagnostics(self.path, 1, False)
        response = client.request('textDocument/definition', {"textDocument": {"uri": self.path.as_uri()}, "position": {"line": 2, "character": 8}})
        self.assertEqual(response['error']['code'], -32803)
        self.assertIn('escapes', response['error']['message'])

    @unittest.skipUnless(shutil.which('nvim'), 'Neovim is not installed')
    def test_real_neovim_uses_standard_lsp_and_does_not_save_formatting(self):
        source = 'main   : IO Unit\nmain = putStrLn  "hello 🌍"\n'
        self.path.write_text(source)
        script = self.root / 'client.lua'
        quoted = lambda value: json.dumps(str(value), ensure_ascii=False)
        script.write_text(f'''vim.opt.runtimepath:append({quoted(ROOT / 'editors/nvim')})
require('fibril').setup({{ keymaps = false }})
vim.cmd('filetype plugin on')
vim.cmd('edit ' .. vim.fn.fnameescape({quoted(self.path)}))
vim.bo.filetype = 'fibril'
assert(vim.wait(15000, function()
  local clients = vim.lsp.get_clients({{ bufnr = 0, name = 'fibril_lsp' }})
  return #clients == 1 and clients[1].initialized
end, 20), 'LSP did not attach')
assert(vim.fn.exists(':FibrilDefinition') == 0, 'legacy navigation command is still installed')
local responses = vim.lsp.buf_request_sync(0, 'textDocument/documentSymbol', {{textDocument={{uri=vim.uri_from_bufnr(0)}}}}, 15000)
assert(responses, 'no symbol response')
for _, response in pairs(responses) do
  assert(not response.err, vim.inspect(response.err))
  assert(response.result[1].name == 'main', vim.inspect(response))
end
vim.lsp.buf.format({{ async = false, timeout_ms = 15000 }})
assert(vim.api.nvim_buf_get_lines(0, 0, 1, false)[1] == 'main : IO Unit', 'formatting did not update buffer')
vim.lsp.stop_client(vim.lsp.get_clients({{bufnr=0}}))
vim.wait(5000, function() return #vim.lsp.get_clients({{bufnr=0}}) == 0 end, 20)
vim.cmd('qa!')
''', encoding='utf-8')
        result = subprocess.run([shutil.which('nvim'), '--headless', '-u', 'NONE', '-l', str(script)], capture_output=True, timeout=45)
        self.assertEqual(result.returncode, 0, result.stdout.decode() + result.stderr.decode())
        self.assertEqual(self.path.read_text(), source)

    def fake(self):
        script = self.root / "fake-compiler"
        marker = self.root / "started"
        script.write_text('#!' + sys.executable + '\nimport sys,json,time\nfrom pathlib import Path\n'
            'if sys.argv[1] == "symbols":\n'
            f' Path({str(marker)!r}).write_text("started")\n time.sleep(0.8)\n'
            'print(json.dumps({"version":1,"coordinates":"unicode-scalars;offset=0;line=1;column=1","accepted":True,"diagnostics":[],"symbols":[]}))\n')
        script.chmod(0o755)
        return script, marker

    def started(self, marker):
        deadline = time.monotonic() + 5
        while not marker.exists():
            if time.monotonic() > deadline:
                self.fail("fake compiler did not start")
            time.sleep(0.01)

    def test_cancellation(self):
        binary, marker = self.fake()
        client = self.client(binary=binary)
        client.open(self.path, self.disk)
        client.diagnostics(self.path, 1, False)
        ident = client.begin("textDocument/documentSymbol", {"textDocument": {"uri": self.path.as_uri()}})
        self.started(marker)
        client.notify("$/cancelRequest", {"id": ident})
        self.assertEqual(client.response(ident)["error"]["code"], -32800)

    def test_stale_response_is_not_applied(self):
        binary, marker = self.fake()
        client = self.client(binary=binary)
        client.open(self.path, self.disk)
        client.diagnostics(self.path, 1, False)
        ident = client.begin("textDocument/documentSymbol", {"textDocument": {"uri": self.path.as_uri()}})
        self.started(marker)
        client.change(self.path, self.disk + '\n', 2)
        self.assertEqual(client.response(ident)["error"]["code"], -32801)

    def test_timeout_is_represented_and_server_survives(self):
        binary, _ = self.fake()
        client = self.client(binary=binary, timeout=0.4)
        client.open(self.path, self.disk)
        client.diagnostics(self.path, 1, False)
        result = client.request("textDocument/documentSymbol", {"textDocument": {"uri": self.path.as_uri()}})
        self.assertEqual(result["error"]["code"], -32803)
        self.assertIn("timed out", result["error"]["message"])
        self.assertEqual(client.request("bogus", {})["error"]["code"], -32601)

    def test_malformed_json_does_not_corrupt_stream(self):
        client = self.client()
        raw = b'{not json}'
        client.process.stdin.write(f"Content-Length: {len(raw)}\r\n\r\n".encode() + raw)
        client.process.stdin.flush()
        self.assertEqual(client.receive(lambda value: value.get("id", "absent") is None)["error"]["code"], -32700)
        self.assertEqual(client.request("bogus", {})["error"]["code"], -32601)
        for raw in [b'{"jsonrpc":"2.0","id":1,"id":2,"method":"bogus"}', '{"x":"λ"}'.encode('utf-16')]:
            client.process.stdin.write(f"Content-Length: {len(raw)}\r\n\r\n".encode() + raw)
            client.process.stdin.flush()
            self.assertEqual(client.receive(lambda value: value.get("id", "absent") is None)["error"]["code"], -32700)


if __name__ == "__main__":
    unittest.main()
