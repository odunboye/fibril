#!/usr/bin/env python3
"""Test against this worktree's library, never a shared cached local package.

`make build` must run first. External dependencies are read from Pack's curated
paths; installation of Fibril itself is confined to build/test-prefix.
"""
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def run(command, *, cwd=ROOT, env=None, capture=False, timeout=300):
    process = subprocess.Popen(command, cwd=cwd, env=env, start_new_session=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None, text=capture)
    try:
        output, error = process.communicate(timeout=timeout)
        if process.returncode:
            if capture:
                print(output or "", end="")
                print(error or "", end="")
            raise SystemExit(process.returncode)
        return (output or "").strip()
    finally:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()


def main():
    env = os.environ.copy()
    pack = shlex.split(env.get("PACK", "pack"))
    compiler = shlex.split(env.get("IDRIS2", "idris2"))
    paths = run(pack + ["--log-level=silence", "package-path"], env=env, capture=True).split(os.pathsep)
    # Pack's local-package key does not distinguish these active worktrees.
    # Keep all external packages but never select its cached Fibril dependency.
    external = [path for path in paths if Path(path).parent.parent.name != "fibril"]
    stage = ROOT / "build/test-prefix"
    if stage.is_symlink() or not stage.resolve().is_relative_to(ROOT):
        raise SystemExit("Refusing a test prefix outside this worktree")
    env["IDRIS2_PREFIX"] = str(stage)
    env["IDRIS2_PACKAGE_PATH"] = os.pathsep.join(external)
    env["IDRIS2_LIBS"] = run(pack + ["--log-level=silence", "libs-path"], env=env, capture=True)
    env.setdefault("CHEZ", shutil.which("chez") or shutil.which("scheme") or "chez")
    installed = Path(run(compiler + ["--dump-installdir", "fibril.ipkg"], env=env, capture=True))
    if not installed.resolve().is_relative_to(stage.resolve()):
        raise SystemExit("Refusing installation outside this worktree's test prefix")
    run(compiler + ["--install", "fibril.ipkg"], env=env)
    env["IDRIS2_PACKAGE_PATH"] = os.pathsep.join([str(installed.parent), *external])
    run(compiler + ["--build", "tests.ipkg"], cwd=ROOT / "test", env=env)
    run([str(ROOT / "test/build/exec/fibril-tests")], env=env)


if __name__ == "__main__":
    main()
