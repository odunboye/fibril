#!/usr/bin/env python3
"""Run the pinned Idris API with lazy termination-error traces.

Only diagnostic call paths change representation; size-change matrices and
termination decisions are unchanged. The installed compiler is never modified.
The private adapter is bootstrapped once under build/host-compiler/.
"""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import signal
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REVISION = "74b33730b6fea649b15e8d01ab099df9effcc7a0"
SOURCE_SHA256 = "19e955759d52f9ae4c6691809941032fa050d667e5ae47be92c1e1429517040d"
MAIN = """module FibrilIdris

import Core.Termination.SizeChange
import Compiler.Common
import Idris.Driver

main : IO ()
main = mainWithCodegens []
"""
PACKAGE = """package fibril-idris
sourcedir = "src"
depends = idris2
modules = Core.Termination.SizeChange, FibrilIdris
main = FibrilIdris
executable = fibril-idris
"""


def pinned_context():
    pack = shlex.split(os.environ.get("PACK", "pack"))

    def query(*args):
        return subprocess.check_output(pack + ["--log-level=silence", *args],
                                       cwd=ROOT, text=True).strip()

    compiler = query("app-path", "idris2")
    paths = {key: query(option) for key, option in (
        ("IDRIS2_PACKAGE_PATH", "package-path"),
        ("IDRIS2_LIBS", "libs-path"), ("IDRIS2_DATA", "data-path"))}
    bootstrap_env = os.environ.copy()
    bootstrap_env.update(paths)
    # A caller's private Fibril test prefix is for the eventual invocation,
    # not for bootstrapping the host compiler API.
    bootstrap_env.pop("IDRIS2_PREFIX", None)
    bootstrap_env.pop("IDRIS2_INC_CGS", None)
    bootstrap_env.pop("IDRIS2_CG", None)
    requested_chez = bootstrap_env.get("CHEZ")
    chez = shutil.which(requested_chez) if requested_chez else None
    if requested_chez and not chez:
        raise RuntimeError(f"CHEZ executable not found: {requested_chez}")
    chez = chez or next((p for name in ("chez", "scheme", "chezscheme")
                         if (p := shutil.which(name))), None)
    if not chez:
        raise RuntimeError("Chez Scheme is required to bootstrap the host compiler")
    # Chez also writes this path into Scheme shebangs; a bare name is invalid.
    bootstrap_env["CHEZ"] = os.path.abspath(chez)
    return compiler, paths, bootstrap_env


def lazy_traces(source):
    """Preserve the algorithm and error paths; defer list concatenation only."""
    if hashlib.sha256(source.encode()).hexdigest() != SOURCE_SHA256:
        raise RuntimeError("Unsupported Idris termination-checker source; "
                           "use make IDRIS2=idris2 build for the stock compiler")
    replacements = (
        ("seq : CallSeq {- f g -}", "seq : Lazy (CallSeq {- f g -})", 1),
        ("show a.seq", "show (force a.seq)", 1),
        ("(a1.seq ++ a2.seq)", "(Delay (force a1.seq ++ force a2.seq))", 1),
        ("MkGraph ch [(l, d2.fullname)]", "MkGraph ch (Delay [(l, d2.fullname)])", 1),
        ("RecPath loop.seq", "RecPath (force loop.seq)", 2),
    )
    for old, new, count in replacements:
        if source.count(old) != count:
            raise RuntimeError(f"Unexpected Idris source at {old!r}")
        source = source.replace(old, new)
    return source


def ensure_compiler(compiler, paths, bootstrap_env):
    version = subprocess.check_output([compiler, "--version"], cwd=ROOT,
                                      env=bootstrap_env, text=True).strip()
    if REVISION[:9] not in version:
        raise RuntimeError(f"Unsupported pinned compiler: {version}; "
                           "use make IDRIS2=idris2 build for the stock compiler")
    sources = [Path(p) / "idris2-0.8.0/Core/Termination/SizeChange.idr"
               for p in paths["IDRIS2_PACKAGE_PATH"].split(os.pathsep)]
    source = next((p for p in sources if p.is_file()), None)
    if source is None:
        raise RuntimeError("Pinned idris2 API sources are missing; install the "
                           "collection's idris2 library, or use make IDRIS2=idris2 build")
    patched = lazy_traces(source.read_text())
    identity = {
        "stock_compiler": compiler, "compiler_version": version,
        "source_sha256": SOURCE_SHA256,
        "patched_sha256": hashlib.sha256(patched.encode()).hexdigest(),
        "driver_sha256": hashlib.sha256((MAIN + PACKAGE).encode()).hexdigest(),
        "platform": platform.system(), "machine": platform.machine(),
        "chez": bootstrap_env["CHEZ"],
    }
    key = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()[:16]
    cache = ROOT / "build/host-compiler" / key
    cache.mkdir(parents=True, exist_ok=True)
    executable = cache / "build/exec/fibril-idris"
    manifest = cache / "manifest.json"
    with (cache / "bootstrap.lock").open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if executable.is_file() and manifest.is_file():
            if json.loads(manifest.read_text()) == identity:
                return executable
        target = cache / "src/Core/Termination/SizeChange.idr"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(patched)
        (cache / "src/FibrilIdris.idr").write_text(MAIN)
        (cache / "fibril-idris.ipkg").write_text(PACKAGE)
        print("Bootstrapping Fibril's private Idris adapter (cached under build/host-compiler).",
              file=sys.stderr, flush=True)
        process = subprocess.Popen(
            [compiler, "--cg", "chez", "--build", "fibril-idris.ipkg"],
            cwd=cache, env=bootstrap_env, stdout=sys.stderr, stderr=sys.stderr,
            start_new_session=True)
        try:
            code = process.wait(timeout=600)
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        if code:
            raise RuntimeError(f"Private compiler bootstrap failed (exit {code})")
        if not executable.is_file():
            raise RuntimeError("Compiler bootstrap produced no executable")
        temporary = manifest.with_suffix(".tmp")
        temporary.write_text(json.dumps(identity, indent=2) + "\n")
        temporary.replace(manifest)
    return executable


def main():
    compiler, paths, bootstrap_env = pinned_context()
    executable = ensure_compiler(compiler, paths, bootstrap_env)
    if sys.argv[1:] == ["--print-compiler"]:
        print(executable)
        return
    env = os.environ.copy()
    # Preserve caller-selected test-prefix filtering and support paths.
    for key, value in paths.items():
        env.setdefault(key, value)
    env["CHEZ"] = bootstrap_env["CHEZ"]
    os.execvpe(str(executable), [str(executable), *sys.argv[1:]], env)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        raise SystemExit(130)
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"fibril-idris: {error}", file=sys.stderr)
        raise SystemExit(1)
