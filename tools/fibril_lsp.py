#!/usr/bin/env python3
"""Fibril stdio LSP. Compiler-backed services over private, bounded snapshots.

Python 3.10+, POSIX. No third-party dependencies, source execution or source writes.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import signal
import stat
import subprocess
import sys
import tempfile
import threading
import time
from urllib.parse import unquote, urlsplit

MAX_FRAME = 8 * 1024 * 1024
MAX_FILE = 65536
MAX_FILES = 1024
MAX_SNAPSHOT = 8 * 1024 * 1024
COORDINATES = "unicode-scalars;offset=0;line=1;column=1"
IGNORED = {".git", "build", "node_modules", "__pycache__", ".venv", ".cache", "dist", "target"}


class LSPError(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


class Cancellation(threading.Event):
    def __init__(self):
        super().__init__()
        self.code = -32800

    def cancel(self, code=-32800):
        self.code = code
        self.set()

    def error(self):
        return LSPError(self.code, "Document/workspace changed during request" if self.code == -32801 else "Request cancelled")


def invalid(message):
    raise LSPError(-32602, message)


def integer(value):
    return isinstance(value, int) and not isinstance(value, bool)


def uri_path(uri):
    if not isinstance(uri, str):
        invalid("Expected a local file URI")
    parsed = urlsplit(uri)
    if (parsed.scheme != "file" or parsed.netloc not in ("", "localhost") or
            parsed.query or parsed.fragment or re.search(r"%(?![0-9a-fA-F]{2})", parsed.path)):
        invalid("Only local file URIs without query/fragment are supported")
    try:
        path = unquote(parsed.path, errors="strict")
        if "\0" in path or not Path(path).is_absolute():
            invalid("Invalid file URI path")
        return Path(path).resolve()
    except (ValueError, UnicodeError, OSError) as error:
        invalid(str(error))


def valid_text(text):
    if not isinstance(text, str):
        invalid("Expected document text")
    try:
        size = len(text.encode("utf-8"))
    except UnicodeError:
        invalid("Document text contains an unpaired surrogate")
    if size > MAX_FILE:
        invalid("Document exceeds the compiler's 65536-byte source limit")
    return text


class Positions:
    """LSP UTF-16 coordinates and Python/compiler scalar offsets; no rounding."""
    def __init__(self, text):
        self.text = text
        self.starts = [0]
        self.ends = []
        for match in re.finditer(r"\r\n|\r|\n", text):
            self.ends.append(match.start())
            self.starts.append(match.end())
        self.ends.append(len(text))

    def offset(self, position):
        if not isinstance(position, dict):
            invalid("Expected an LSP position")
        line, units = position.get("line"), position.get("character")
        if not integer(line) or not integer(units) or not 0 <= line < len(self.starts) or units < 0:
            invalid("Position is outside the document")
        index = self.starts[line]
        used = 0
        while index < self.ends[line] and used < units:
            used += 2 if ord(self.text[index]) > 0xFFFF else 1
            index += 1
        if used != units:
            invalid("Position splits a UTF-16 surrogate pair or exceeds the line")
        return index

    def point(self, offset):
        if not integer(offset) or not 0 <= offset <= len(self.text):
            raise LSPError(-32803, "Compiler returned an invalid scalar offset")
        import bisect
        line = bisect.bisect_right(self.starts, offset) - 1
        content = self.text[self.starts[line]:min(offset, self.ends[line])]
        return {"line": line, "character": len(content.encode("utf-16-le")) // 2}

    def compiler_point(self, point):
        if not isinstance(point, dict) or not integer(point.get("offset")):
            raise LSPError(-32803, "Compiler response lacks scalar offsets")
        return self.point(point["offset"])

    def compiler_range(self, value):
        if not isinstance(value, dict):
            raise LSPError(-32803, "Compiler returned an invalid range")
        start, end = value.get("start"), value.get("end")
        if not isinstance(start, dict) or not isinstance(end, dict) or start.get("offset", -1) > end.get("offset", -1):
            raise LSPError(-32803, "Compiler returned a reversed range")
        return {"start": self.compiler_point(start), "end": self.compiler_point(end)}

    def location(self, position):
        offset = self.offset(position)
        point = self.point(offset)
        return point["line"] + 1, offset - self.starts[point["line"]] + 1


def changed_text(text, changes):
    if not isinstance(changes, list) or not 1 <= len(changes) <= 128:
        invalid("Expected 1..128 ordered content changes")
    for change in changes:
        if not isinstance(change, dict):
            invalid("Invalid content change")
        replacement = valid_text(change.get("text"))
        if "range" not in change:
            text = replacement
        else:
            span = change["range"]
            if not isinstance(span, dict):
                invalid("Invalid edit range")
            positions = Positions(text)
            start, end = positions.offset(span.get("start")), positions.offset(span.get("end"))
            if end < start:
                invalid("Reversed edit range")
            if "rangeLength" in change and change["rangeLength"] != len(text[start:end].encode("utf-16-le")) // 2:
                invalid("rangeLength does not match the replaced UTF-16 text")
            text = text[:start] + replacement + text[end:]
        valid_text(text)
    return text


@dataclass(frozen=True)
class Document:
    uri: str
    path: Path
    version: int
    text: str


@dataclass(frozen=True)
class View:
    epoch: int
    documents: dict
    roots: tuple
    options: dict

    def uri(self, path):
        return next((doc.uri for doc in self.documents.values() if doc.path == path), path.as_uri())


def fingerprint(path):
    try:
        value = path.stat()
        return value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns
    except OSError:
        return None


class Snapshot:
    """A workspace copy with all open buffers overlaid, never symlinked sources."""
    def __init__(self, view, document, directory, backend, cancel, local_only=False):
        self.view, self.document = view, document
        self.directory, self.backend, self.cancel = Path(directory).resolve(), backend, cancel
        roots = [root for root in view.roots if document.path.is_relative_to(root)]
        self.root = max(roots, key=lambda p: len(p.parts)) if roots else document.path.parent
        if self.directory.is_relative_to(self.root):
            raise LSPError(-32803, "Workspace includes temporary snapshot storage; use a narrower project root")
        opts = {} if local_only else view.options
        self.manifest = None
        configured = opts.get("manifest")
        if configured:
            self.manifest = self.config_path(configured)
        elif not local_only:
            for parent in (document.path.parent, *document.path.parents):
                if not parent.is_relative_to(self.root):
                    break
                candidate = parent / "fibril.yaml"
                if candidate.is_file():
                    self.manifest = candidate
                    break
        module = None if local_only else re.search(r"(?m)^module\s+([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*)\s*$", document.text)
        self.source_root = None
        self.entry = document.path
        if not self.manifest and (opts.get("sourceDir") or module):
            if opts.get("sourceDir"):
                self.source_root = self.config_path(opts["sourceDir"])
            else:
                self.source_root = document.path.parent
                for _ in module.group(1).split(".")[1:]:
                    self.source_root = self.source_root.parent
            if not self.source_root.is_relative_to(self.root):
                raise LSPError(-32803, "Inferred source root escapes workspace; configure sourceDir/workspace root")
            if opts.get("entry"):
                self.entry = self.config_path(opts["entry"])
            elif (self.source_root / "Main.fib").is_file() or any(d.path == self.source_root / "Main.fib" for d in view.documents.values()):
                self.entry = self.source_root / "Main.fib"
        self.data = {}
        self.texts, self.position_maps = {}, {}
        self.observed = {}
        if self.manifest or self.source_root:
            self.copy_tree()
        else:
            self.observed[document.path] = fingerprint(document.path)
            self.add(document.path, document.text.encode("utf-8"))
        for doc in view.documents.values():
            if doc.path.is_relative_to(self.root) and (self.manifest or self.source_root or doc.path == document.path):
                self.add(doc.path, doc.text.encode("utf-8"))
        if self.manifest:
            self.check_dependencies(self.manifest, set())

    def config_path(self, name):
        if not isinstance(name, str):
            invalid("Project options must be paths")
        path = (self.root / name).resolve()
        if not path.is_relative_to(self.root):
            invalid("Project option escapes workspace root")
        return path

    def mapped(self, original):
        if not original.is_relative_to(self.root):
            raise LSPError(-32803, "Source path escapes snapshot")
        return self.directory / original.relative_to(self.root)

    def original(self, copied):
        path = Path(copied).resolve()
        if not path.is_relative_to(self.directory):
            raise LSPError(-32803, "Compiler response escapes the private snapshot")
        original = self.root / path.relative_to(self.directory)
        if original not in self.data:
            raise LSPError(-32803, "Compiler referenced a source absent from the snapshot")
        return original

    def text(self, original):
        if original not in self.texts:
            self.texts[original] = self.data[original].decode("utf-8", errors="replace")
        return self.texts[original]

    def positions(self, original):
        if original not in self.position_maps:
            self.position_maps[original] = Positions(self.text(original))
        return self.position_maps[original]

    def add(self, path, data):
        if self.cancel.is_set():
            raise self.cancel.error()
        if len(data) > MAX_FILE or len(self.data) >= MAX_FILES and path not in self.data:
            raise LSPError(-32803, "Source snapshot exceeds file admission limits")
        if sum(map(len, self.data.values())) - len(self.data.get(path, b"")) + len(data) > MAX_SNAPSHOT:
            raise LSPError(-32803, "Source snapshot exceeds 8 MiB")
        target = self.mapped(path)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        self.data[path] = data
        self.texts.pop(path, None)
        self.position_maps.pop(path, None)

    def copy_tree(self):
        directories = 0
        for parent, dirs, files in os.walk(self.root, followlinks=False):
            self.observed[Path(parent)] = fingerprint(Path(parent))
            directories += 1
            if directories > 4096:
                raise LSPError(-32803, "Workspace directory admission exceeded")
            dirs[:] = sorted(d for d in dirs if d not in IGNORED and not d.startswith(".tmp") and not (Path(parent) / d).is_symlink())
            for name in sorted(files):
                if not (name.endswith(".fib") or name == "fibril.yaml"):
                    continue
                path = Path(parent) / name
                # No following workspace symlinks, FIFOs or devices. A missing
                # dependency is then reported by the ordinary compiler loader.
                flags = os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW
                try:
                    fd = os.open(path, flags)
                except OSError:
                    continue
                with os.fdopen(fd, "rb") as source:
                    before = os.fstat(source.fileno())
                    if not stat.S_ISREG(before.st_mode):
                        continue
                    data = source.read(MAX_FILE + 1)
                    after = os.fstat(source.fileno())
                if (before.st_ino, before.st_size, before.st_mtime_ns) != (after.st_ino, after.st_size, after.st_mtime_ns):
                    raise LSPError(-32801, "Source changed during snapshot capture")
                self.observed[path] = (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns)
                self.add(path, data)

    def verify_disk(self):
        if any(fingerprint(path) != value for path, value in self.observed.items()):
            raise LSPError(-32801, "Workspace files changed during request")

    def call(self, args, rejection=False):
        packet = self.backend([str(arg) for arg in args], self.directory, self.cancel, rejection)
        if not integer(packet.get("version")) or packet["version"] not in (1, 2):
            raise LSPError(-32803, "Unsupported compiler response version")
        if "coordinates" in packet and packet["coordinates"] != COORDINATES:
            raise LSPError(-32803, "Unsupported compiler coordinate system")
        for source in packet.get("sources", []):
            path = self.original(source["path"])
            if source.get("text") != self.text(path):
                raise LSPError(-32801, "Compiler source snapshot mismatch")
        return packet

    def check_dependencies(self, manifest, seen):
        if manifest in seen:
            return  # The compiler diagnoses dependency cycles itself.
        if len(seen) >= 64 or manifest not in self.data:
            raise LSPError(-32803, "Package dependency is outside the workspace snapshot or exceeds admission")
        seen.add(manifest)
        packet = self.call(["manifest", self.mapped(manifest)])
        for dependency in packet.get("dependencies", []):
            folder = (manifest.parent / dependency["path"]).resolve()
            if not folder.is_relative_to(self.root):
                raise LSPError(-32803, "Package dependency escapes workspace; open its common parent as workspace")
            self.check_dependencies(folder / "fibril.yaml", seen)

    def check(self):
        if self.manifest:
            return self.call(["check", "--json", "--package", self.mapped(self.manifest)], True)
        if self.source_root:
            return self.call(["check", "--json", "--source-dir", self.mapped(self.source_root), self.mapped(self.entry)], True)
        return self.call(["check", "--json", self.mapped(self.document.path)], True)

    def navigation(self, method, line, column):
        query = self.mapped(self.document.path)
        if self.manifest:
            packet = self.call([method, "--package", self.mapped(self.manifest), line, column, query])
        elif self.source_root:
            packet = self.call([method, "--source-dir", self.mapped(self.source_root), "--entry", self.mapped(self.entry), line, column, query])
        else:
            packet = self.call([method, line, column, query])
        if (self.manifest or self.source_root) and (packet.get("checked") is not True or packet.get("query") != str(query)):
            raise LSPError(-32803, "Navigation response is not checked for this query")
        packet["_lsp_locations"] = {source["path"]: self.original(source["path"]) for source in packet.get("sources", [])}
        return packet

    def location(self, target, packet):
        path = packet["_lsp_locations"].get(target["path"])
        if path is None:
            self.original(target["path"])  # Reject escapes before reporting an absent graph member.
            raise LSPError(-32803, "Navigation location is not in the checked source graph")
        return {"uri": self.view.uri(path), "range": self.positions(path).compiler_range(target["range"])}

    def definition(self, line, column, links=False):
        packet = self.navigation("definition", line, column)
        target = packet.get("definition")
        if target is None:
            return None
        if "path" not in target:
            return {"uri": self.document.uri, "range": Positions(self.document.text).compiler_range(target)}
        location = self.location(target, packet)
        if not links:
            return location
        origin = packet.get("origin")
        if origin is None or self.original(origin["path"]) != self.document.path:
            raise LSPError(-32803, "Definition response lacks a valid query origin")
        return [{"originSelectionRange": Positions(self.document.text).compiler_range(origin["range"]),
                 "targetUri": location["uri"], "targetRange": location["range"], "targetSelectionRange": location["range"]}]

    def references(self, line, column, include_declaration):
        packet = self.navigation("references", line, column)
        references = packet.get("references")
        if not isinstance(references, list):
            raise LSPError(-32803, "Invalid compiler reference index")
        result, seen = [], set()
        for reference in references:
            if not isinstance(reference.get("declaration"), bool):
                raise LSPError(-32803, "Reference index lacks declaration classification")
            if include_declaration or not reference["declaration"]:
                location = self.location(reference, packet)
                span = location["range"]
                key = (location["uri"], span["start"]["line"], span["start"]["character"], span["end"]["line"], span["end"]["character"])
                if key not in seen:
                    seen.add(key)
                    result.append(location)
        return result


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("Duplicate JSON object key")
        result[key] = value
    return result


def read_frame(stream):
    headers, size = {}, 0
    while True:
        line = stream.readline(8193)
        if not line:
            if size:
                raise ValueError("Truncated LSP headers")
            return None
        size += len(line)
        if size > 8192 or not line.endswith(b"\r\n"):
            raise ValueError("Invalid or oversized LSP headers")
        if line == b"\r\n":
            break
        key, separator, value = line.decode("ascii").partition(":")
        key = key.strip().lower()
        if not separator or key in headers:
            raise ValueError("Malformed or duplicate LSP header")
        headers[key] = value.strip()
    content_type = headers.get("content-type", "").lower()
    if "charset=" in content_type and content_type.split("charset=", 1)[1].strip() not in ("utf-8", "utf8"):
        raise ValueError("LSP messages must use UTF-8")
    length = headers.get("content-length", "")
    if not length.isascii() or not length.isdecimal() or not 0 < int(length) <= MAX_FRAME:
        raise ValueError("Missing or invalid Content-Length")
    remaining, chunks = int(length), []
    while remaining:
        chunk = stream.read(remaining)
        if not chunk:
            raise ValueError("Truncated LSP body")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


class Server:
    def __init__(self, binary, incoming, outgoing, timeout=15):
        self.binary, self.incoming, self.outgoing, self.timeout = binary, incoming, outgoing, timeout
        self.lock, self.output_lock = threading.RLock(), threading.Lock()
        self.executor = ThreadPoolExecutor(max_workers=1, thread_name_prefix="fibril-compiler")
        self.work_context = threading.local()
        self.documents, self.requests = {}, {}
        self.roots, self.options = (), {}
        self.epoch = 0
        self.initialized = self.shutdown = False
        self.versioned_edits = False
        self.definition_links = False
        self.diagnostic_future = None
        self.diagnostic_cancel = Cancellation()
        self.published = set()
        self.watched = {}
        self.stopping = threading.Event()
        self.watcher = threading.Thread(target=self.watch_disk, name="fibril-files", daemon=True)
        self.watcher.start()

    def send(self, packet):
        data = json.dumps({"jsonrpc": "2.0", **packet}, ensure_ascii=True, allow_nan=False).encode("utf-8")
        if len(data) > MAX_FRAME:
            raise LSPError(-32803, "Server response admission exceeded")
        with self.output_lock:
            self.outgoing.write(f"Content-Length: {len(data)}\r\n\r\n".encode("ascii") + data)
            self.outgoing.flush()

    def error(self, ident, error):
        self.send({"id": ident, "error": {"code": error.code, "message": str(error)}})

    def log(self, message):
        self.send({"method": "window/logMessage", "params": {"type": 2, "message": str(message)}})

    def backend(self, args, directory, cancel, rejection):
        with tempfile.TemporaryFile() as output, tempfile.TemporaryFile() as errors:
            process = subprocess.Popen([self.binary, *args], cwd=directory, stdout=output,
                                       stderr=errors, start_new_session=True, stdin=subprocess.DEVNULL)
            deadline = time.monotonic() + self.timeout
            try:
                while process.poll() is None:
                    if cancel.wait(0.02):
                        raise cancel.error()
                    if time.monotonic() >= deadline:
                        raise LSPError(-32803, "Compiler request timed out")
                    if os.fstat(output.fileno()).st_size > MAX_FRAME or os.fstat(errors.fileno()).st_size > MAX_FRAME:
                        raise LSPError(-32803, "Compiler response admission exceeded")
                output.seek(0)
                raw = output.read(MAX_FRAME + 1)
                errors.seek(0)
                message = errors.read(4096).decode("utf-8", errors="replace").replace(str(directory), "<snapshot>")
                if len(raw) > MAX_FRAME:
                    raise LSPError(-32803, "Compiler response admission exceeded")
                if process.returncode and not rejection:
                    raise LSPError(-32803, message.strip() or "Compiler service rejected the request")
                try:
                    packet = json.loads(raw.decode("utf-8"))
                except (ValueError, UnicodeError, RecursionError):
                    raise LSPError(-32803, message.strip() or "Compiler did not return a JSON report")
                if not isinstance(packet, dict):
                    raise LSPError(-32803, "Invalid compiler response")
                if rejection and (not isinstance(packet.get("accepted"), bool) or packet["accepted"] != (process.returncode == 0)):
                    raise LSPError(-32803, "Compiler checking status disagrees with its report")
                return packet
            finally:
                # Only this request's fresh process group, never other sessions.
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                process.wait()

    def watch_disk(self):
        while not self.stopping.wait(0.25):
            with self.lock:
                if self.shutdown:
                    return
                observed = dict(self.watched)
            current = {path: fingerprint(path) for path in observed}
            if current != observed:
                with self.lock:
                    if not self.shutdown and self.watched == observed:
                        self.watched = current
                        self.refresh()

    def view(self):
        return View(self.epoch, dict(self.documents), self.roots, dict(self.options))

    def diagnostics(self, view, cancel):
        groups = {}
        checked = set()
        observed = {}
        try:
            for doc in view.documents.values():
                if cancel.is_set():
                    return
                try:
                    with tempfile.TemporaryDirectory(prefix="fibril-lsp-") as directory:
                        snapshot = Snapshot(view, doc, directory, self.backend, cancel)
                        key = (snapshot.manifest,) if snapshot.manifest else (snapshot.source_root, snapshot.entry)
                        if key in checked:
                            continue
                        checked.add(key)
                        packet = snapshot.check()
                        snapshot.verify_disk()
                        observed.update(snapshot.observed)
                        if packet.get("accepted") is True and (snapshot.manifest or snapshot.source_root) and not any(source.get("path") == str(snapshot.mapped(doc.path)) for source in packet.get("sources", [])):
                            if not re.search(r"(?m)^module\s", doc.text):
                                packet = snapshot.call(["check", "--json", snapshot.mapped(doc.path)], True)
                            else:
                                groups.setdefault(doc.uri, []).append({"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}}, "severity": 2, "source": "fibril-lsp", "message": "Document is outside the checked entry/inventory; import it, list it in the manifest, or configure entry."})
                        for diagnostic in packet.get("diagnostics", []):
                            path = snapshot.original(diagnostic["path"]) if diagnostic.get("path") else doc.path
                            mapper = Positions(snapshot.text(path))
                            point = mapper.compiler_point(diagnostic["position"]) if diagnostic.get("position") else {"line": 0, "character": 0}
                            item = {"range": {"start": point, "end": point}, "severity": 1,
                                    "source": "fibril", "message": diagnostic.get("message", "Checking failed"),
                                    "code": diagnostic.get("stage", "checking")}
                            uri = view.uri(path)
                            if item not in groups.setdefault(uri, []):
                                groups[uri].append(item)
                except LSPError as error:
                    if error.code == -32800:
                        return
                    if error.code == -32801:
                        with self.lock:
                            if self.epoch == view.epoch and not self.shutdown:
                                self.refresh()
                        return
                    groups.setdefault(doc.uri, []).append({"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}},
                        "severity": 1, "source": "fibril-lsp", "message": str(error)})
            with self.lock:
                if cancel.is_set() or self.epoch != view.epoch or self.shutdown:
                    return
                uris = self.published | set(groups) | set(view.documents)
                for uri in sorted(uris):
                    params = {"uri": uri, "diagnostics": groups.get(uri, [])}
                    if uri in view.documents:
                        params["version"] = view.documents[uri].version
                    self.send({"method": "textDocument/publishDiagnostics", "params": params})
                self.published = set(groups) | set(view.documents)
                self.watched = observed
        except Exception as error:
            if not cancel.is_set():
                self.log(f"Diagnostic service failed: {error}")

    def refresh(self):
        self.epoch += 1
        self.diagnostic_cancel.cancel()
        self.diagnostic_cancel = Cancellation()
        for cancel in self.requests.values():
            cancel.cancel(-32801)
        if self.diagnostic_future:
            self.diagnostic_future.cancel()
        self.diagnostic_future = self.executor.submit(self.diagnostics, self.view(), self.diagnostic_cancel)

    def service(self, method, params, view, cancel):
        if not isinstance(params.get("textDocument"), dict):
            invalid("Expected textDocument parameters")
        uri = params["textDocument"].get("uri")
        doc = view.documents.get(uri)
        if doc is None:
            invalid("Open the document before requesting language services")
        mapper = Positions(doc.text)
        with tempfile.TemporaryDirectory(prefix="fibril-lsp-") as directory:
            local_only = method in {"textDocument/documentSymbol", "textDocument/formatting", "textDocument/completion"}
            snapshot = Snapshot(view, doc, directory, self.backend, cancel, local_only)
            # Keep the immutable snapshot for the final disk-freshness check.
            self.work_context.snapshot = snapshot
            path = snapshot.mapped(doc.path)
            if method == "textDocument/documentSymbol":
                packet = snapshot.call(["symbols", path])
                return [{"name": symbol["name"], "kind": 12,
                         "range": mapper.compiler_range(symbol["range"]),
                         "selectionRange": mapper.compiler_range(symbol["selection"])} for symbol in packet["symbols"]]
            if method == "textDocument/formatting":
                packet = snapshot.call(["format", "--json", path])
                if packet.get("original") != doc.text:
                    raise LSPError(-32801, "Formatting source snapshot mismatch")
                formatted = valid_text(packet.get("formatted"))
                return [] if formatted == doc.text else [{"range": {"start": {"line": 0, "character": 0}, "end": mapper.point(len(doc.text))}, "newText": formatted}]
            position = params.get("position")
            line, column = mapper.location(position)
            if method == "textDocument/completion":
                # shortcut: current file + Prelude top-level names only, no scope/type awareness; upgrade with a compiler "scope" query.
                offset = mapper.offset(position)
                prefix = re.search(r"[A-Za-z0-9_']*$", doc.text[:offset]).group(0)
                names = {symbol["name"] for symbol in snapshot.call(["symbols", path])["symbols"]}
                prelude = Path(self.binary).resolve().parents[2] / "stdlib" / "Prelude.fib"
                if prelude.is_file() and prelude != doc.path:
                    names |= {symbol["name"] for symbol in snapshot.call(["symbols", prelude])["symbols"]}
                return {"isIncomplete": False, "items": [{"label": name, "kind": 3} for name in sorted(names) if name.startswith(prefix)]}
            if method == "textDocument/definition":
                return snapshot.definition(line, column, self.definition_links)
            if method == "textDocument/hover":
                packet = snapshot.call(["reference", line, column, path])
                reference = packet.get("reference")
                if reference:
                    if reference["kind"] == "builtin-documentation":
                        value = "\n".join(reference["lines"])
                    else:
                        source = reference["source"]
                        start = reference["range"]["start"]["offset"]
                        value = source[source.rfind("\n", 0, start) + 1:source.find("\n", start) if "\n" in source[start:] else len(source)]
                    return {"contents": {"kind": "plaintext", "value": value}}
                target = snapshot.definition(line, column)
                if not target:
                    return None
                original = uri_path(target["uri"])
                text = snapshot.text(original)
                index = Positions(text).offset(target["range"]["start"])
                return {"contents": {"kind": "plaintext", "value": text[index:].splitlines()[0][:512]}}
            if method == "textDocument/references":
                context = params.get("context", {})
                if not isinstance(context, dict) or not isinstance(context.get("includeDeclaration", False), bool):
                    invalid("References require a boolean includeDeclaration")
                include_declaration = context.get("includeDeclaration", False)
                if snapshot.manifest or snapshot.source_root:
                    return snapshot.references(line, column, include_declaration)
                packet = snapshot.call(["references", line, column, path])
                ranges = [mapper.compiler_range(span) for span in packet["references"]]
                if not include_declaration:
                    definition = snapshot.call(["definition", line, column, path]).get("definition")
                    declarations = [mapper.compiler_range(definition)] if definition else []
                    for symbol in snapshot.call(["symbols", path])["symbols"]:
                        pair = [mapper.compiler_range(symbol[key]) for key in ("selection", "definitionSelection")]
                        if any(span in declarations for span in pair):
                            declarations += pair
                    ranges = [span for span in ranges if span not in declarations]
                return [{"uri": doc.uri, "range": span} for span in ranges]
            if method == "textDocument/rename":
                if not self.versioned_edits:
                    raise LSPError(-32803, "Rename requires client support for versioned documentChanges")
                name = params.get("newName")
                if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{0,255}", name):
                    invalid("Rename requires an ASCII identifier of 1..256 characters")
                if snapshot.manifest or snapshot.source_root:
                    return self.project_rename(snapshot, view, line, column, name)
                packet = snapshot.call(["rename-preview", line, column, name, path])
                edits = [{"range": mapper.compiler_range(edit["range"]), "newText": edit["newText"]} for edit in packet["edits"]]
                return {"documentChanges": [{"textDocument": {"uri": doc.uri, "version": doc.version}, "edits": edits}]}
            raise LSPError(-32601, "Method not found")

    def project_rename(self, snapshot, view, line, column, name):
        locations = snapshot.references(line, column, True)
        if not locations:
            raise LSPError(-32803, "No checked symbol at this position")
        by_file, old = {}, set()
        for location in locations:
            path = uri_path(location["uri"])
            text = snapshot.text(path)
            mapper, span = Positions(text), location["range"]
            old.add(text[mapper.offset(span["start"]):mapper.offset(span["end"])])
            by_file.setdefault(location["uri"], []).append({"range": span, "newText": name})
        if len(old) != 1 or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", next(iter(old))):
            raise LSPError(-32803, "Project rename supports plain identifiers only; occurrences disagree or are qualified")
        # Conservative capture guard: the compiler cannot capture-check across files, so refuse any file already using newName.
        if any(re.search(rf"(?<![A-Za-z0-9_']){name}(?![A-Za-z0-9_'])", snapshot.text(uri_path(uri))) for uri in by_file):
            raise LSPError(-32803, f"Rename refused: {name} already appears in an affected file")
        docs = {document.uri: document.version for document in view.documents.values()}
        return {"documentChanges": [{"textDocument": {"uri": uri, "version": docs.get(uri)}, "edits": edits} for uri, edits in by_file.items()]}

    def work(self, ident, method, params, view, cancel):
        try:
            if cancel.is_set():
                raise cancel.error()
            self.work_context.snapshot = None
            result = self.service(method, params, view, cancel)
            if self.work_context.snapshot:
                self.work_context.snapshot.verify_disk()
            with self.lock:
                if cancel.is_set():
                    raise cancel.error()
                if self.epoch != view.epoch:
                    raise LSPError(-32801, "Document/workspace changed during request")
                self.send({"id": ident, "result": result})
        except LSPError as error:
            self.error(ident, error)
        except Exception as error:
            self.error(ident, LSPError(-32603, f"Language service failed: {error}"))
        finally:
            self.work_context.snapshot = None
            with self.lock:
                self.requests.pop(ident, None)

    def dispatch(self, message):
        if not isinstance(message, dict) or message.get("jsonrpc") != "2.0" or not isinstance(message.get("method"), str):
            self.error(None, LSPError(-32600, "Invalid JSON-RPC request; batches are unsupported"))
            return None
        method, ident = message["method"], message.get("id")
        request = "id" in message
        if request and not (integer(ident) or isinstance(ident, str)):
            self.error(None, LSPError(-32600, "Request ID must be an integer or string"))
            return None
        params = message.get("params", {})
        if params is None:
            params = {}
        if not isinstance(params, dict):
            raise LSPError(-32602, "Expected object parameters")
        if method == "exit" and not request:
            return 0 if self.shutdown else 1
        if method == "initialize" and request:
            if self.initialized:
                raise LSPError(-32600, "Server is already initialized")
            folders = params.get("workspaceFolders")
            if folders is not None and not isinstance(folders, list):
                invalid("workspaceFolders must be a list")
            self.roots = tuple(uri_path(folder["uri"]) for folder in folders) if folders else ((uri_path(params["rootUri"]),) if params.get("rootUri") else ())
            options = params.get("initializationOptions") or {}
            if not isinstance(options, dict) or set(options) - {"sourceDir", "entry", "manifest"}:
                invalid("Supported initializationOptions: sourceDir, entry, manifest")
            if any(not isinstance(value, str) or not value for value in options.values()):
                invalid("Project options must be nonempty paths")
            self.options = options
            self.versioned_edits = params.get("capabilities", {}).get("workspace", {}).get("workspaceEdit", {}).get("documentChanges") is True
            self.definition_links = params.get("capabilities", {}).get("textDocument", {}).get("definition", {}).get("linkSupport") is True
            self.initialized = True
            self.send({"id": ident, "result": {"serverInfo": {"name": "fibril-lsp", "version": "0.1.0"}, "capabilities": {
                "positionEncoding": "utf-16", "textDocumentSync": {"openClose": True, "change": 2, "save": {"includeText": False}},
                "definitionProvider": True, "referencesProvider": True, "completionProvider": {}, "hoverProvider": True,
                "documentSymbolProvider": True, "documentFormattingProvider": True, "renameProvider": self.versioned_edits,
                "workspace": {"workspaceFolders": {"supported": True, "changeNotifications": True}}}}})
            return None
        if not self.initialized:
            if request:
                raise LSPError(-32002, "Server not initialized")
            return None
        if self.shutdown:
            if request:
                raise LSPError(-32600, "Server has shut down")
            return None
        if method == "shutdown" and request:
            self.shutdown = True
            self.diagnostic_cancel.cancel()
            for cancel in self.requests.values():
                cancel.cancel()
            self.send({"id": ident, "result": None})
            return None
        if method == "$/cancelRequest" and not request:
            target = params.get("id")
            if not (integer(target) or isinstance(target, str)):
                invalid("Cancellation ID must be an integer or string")
            cancel = self.requests.get(target)
            if cancel:
                cancel.cancel()
            return None
        if not request:
            self.notification(method, params)
            return None
        supported = {"textDocument/definition", "textDocument/references", "textDocument/hover", "textDocument/documentSymbol", "textDocument/formatting", "textDocument/rename", "textDocument/completion"}
        if method not in supported:
            raise LSPError(-32601, f"Method not found: {method}")
        if ident in self.requests:
            raise LSPError(-32600, "Duplicate outstanding request ID")
        if len(self.requests) >= 64:
            raise LSPError(-32803, "Too many outstanding requests")
        cancel = Cancellation()
        self.requests[ident] = cancel
        self.executor.submit(self.work, ident, method, params, self.view(), cancel)
        return None

    def notification(self, method, params):
        if method in ("initialized", "$/setTrace"):
            return
        if method == "workspace/didChangeWorkspaceFolders":
            event = params["event"]
            roots = set(self.roots)
            roots -= {uri_path(item["uri"]) for item in event.get("removed", [])}
            roots |= {uri_path(item["uri"]) for item in event.get("added", [])}
            self.roots = tuple(sorted(roots))
            self.refresh()
            return
        if method == "workspace/didChangeWatchedFiles":
            self.refresh()
            return
        if method not in {"textDocument/didOpen", "textDocument/didChange", "textDocument/didClose", "textDocument/didSave"}:
            return
        item = params["textDocument"]
        uri = item["uri"]
        path = uri_path(uri)
        if path.suffix != ".fib":
            invalid("Only .fib source documents are supported")
        if method == "textDocument/didOpen":
            if uri in self.documents or any(doc.path == path for doc in self.documents.values()):
                invalid("Document is already open, possibly through another URI")
            version = item.get("version")
            if not integer(version) or len(self.documents) >= 64:
                invalid("Invalid document version or too many open documents")
            self.documents[uri] = Document(uri, path, version, valid_text(item.get("text")))
        elif uri not in self.documents:
            invalid("Document is not open")
        elif method == "textDocument/didChange":
            old = self.documents[uri]
            version = item.get("version")
            if not integer(version) or version <= old.version:
                invalid("Document versions must increase monotonically")
            self.documents[uri] = Document(uri, path, version, changed_text(old.text, params.get("contentChanges")))
        elif method == "textDocument/didClose":
            del self.documents[uri]
        self.refresh()

    def run(self):
        try:
            while True:
                raw = read_frame(self.incoming)
                if raw is None:
                    return 0 if self.shutdown else 1
                try:
                    message = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_object,
                        parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
                except (ValueError, UnicodeError, RecursionError):
                    self.error(None, LSPError(-32700, "Invalid JSON"))
                    continue
                try:
                    with self.lock:
                        status = self.dispatch(message)
                    if status is not None:
                        return status
                except (LSPError, KeyError, TypeError, ValueError, AttributeError) as error:
                    error = error if isinstance(error, LSPError) else LSPError(-32602, "Malformed method parameters")
                    if isinstance(message, dict) and "id" in message:
                        self.error(message.get("id"), error)
                    else:
                        self.log(error)
        except (ValueError, UnicodeError, OSError) as error:
            print(f"fibril-lsp transport: {error}", file=sys.stderr)
            return 2
        finally:
            with self.lock:
                self.shutdown = True
                self.diagnostic_cancel.cancel()
                for cancel in self.requests.values():
                    cancel.cancel()
            self.stopping.set()
            self.watcher.join(timeout=2)
            self.executor.shutdown(wait=True, cancel_futures=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fibril", type=Path, default=Path(__file__).resolve().parents[1] / "build/exec/fibril")
    parser.add_argument("--timeout", type=float, default=15, help="Per-compiler-process deadline in seconds (0.1..120)")
    args = parser.parse_args()
    binary = args.fibril.resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        parser.error("Build Fibril first, or provide --fibril /path/to/executable")
    if not 0.1 <= args.timeout <= 120:
        parser.error("--timeout must be 0.1..120 seconds")
    def terminate(_signal, _frame):
        raise SystemExit(0)
    signal.signal(signal.SIGTERM, terminate)
    return Server(str(binary), sys.stdin.buffer, sys.stdout.buffer, args.timeout).run()


if __name__ == "__main__":
    sys.exit(main())
