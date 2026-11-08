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


def prepare_environment(*, fresh=False):
    """Stage once per runner invocation; child suites only read this package."""
    env = os.environ.copy()
    stage = ROOT / "build/test-prefix"
    if stage.is_symlink() or not stage.resolve().is_relative_to(ROOT):
        raise SystemExit("Refusing a test prefix outside this worktree")
    prepared = env.pop("FIBRIL_TEST_PACKAGE", None)
    if prepared and not fresh:
        package = Path(prepared)
        if (env.get("IDRIS2_PREFIX") != str(stage)
                or not package.resolve().is_relative_to(stage.resolve())
                or not (package / "fibril.ipkg").is_file()):
            raise SystemExit("Invalid prepared test package")
        env["FIBRIL_TEST_PACKAGE"] = prepared
        return env
    pack = shlex.split(env.get("PACK", "pack"))
    compiler = shlex.split(env["IDRIS2"]) if env.get("IDRIS2") else [str(ROOT / "tools/fibril_idris.py")]

    def pack_path(flag):
        output = run(pack + ["--log-level=silence", flag], env=env, capture=True)
        # Pack sometimes prints cache warnings on stdout. Never use those as paths.
        paths = [line for line in output.splitlines() if line.startswith("/")]
        if len(paths) != 1:
            raise SystemExit(f"Ambiguous Pack {flag}: {output}")
        return paths[0]

    paths = pack_path("package-path").split(os.pathsep)
    # Pack's local-package key does not distinguish these active worktrees.
    # Keep all external packages but never select its cached Fibril dependency.
    external = [path for path in paths if Path(path).parent.parent.name != "fibril"]
    env["IDRIS2_PREFIX"] = str(stage)
    env["IDRIS2_PACKAGE_PATH"] = os.pathsep.join(external)
    env["IDRIS2_LIBS"] = pack_path("libs-path")
    # Direct compiler paths do not supply the curated shim's support data path.
    env["IDRIS2_DATA"] = pack_path("data-path")
    env.setdefault("CHEZ", shutil.which("chez") or shutil.which("scheme") or "chez")
    installed = Path(run(compiler + ["--dump-installdir", "fibril.ipkg"], env=env, capture=True))
    if not installed.resolve().is_relative_to(stage.resolve()):
        raise SystemExit("Refusing installation outside this worktree's test prefix")
    run(compiler + ["--install", "fibril.ipkg"], env=env)
    env["IDRIS2_PACKAGE_PATH"] = os.pathsep.join([str(installed.parent), *external])
    env["FIBRIL_TEST_PACKAGE"] = str(installed)
    return env


def main():
    env = prepare_environment()
    compiler = shlex.split(env["IDRIS2"]) if env.get("IDRIS2") else [str(ROOT / "tools/fibril_idris.py")]
    run(compiler + ["--build", "tests.ipkg"], cwd=ROOT / "test", env=env)
    run([str(ROOT / "test/build/exec/fibril-tests")], env=env)


if __name__ == "__main__":
    main()
