#!/usr/bin/env python3
"""Build an optional embedding experiment; never install Python or packages."""
import os
from pathlib import Path
import shlex
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def output(args):
    return subprocess.check_output(args, text=True, timeout=30).strip()


def main():
    config = os.environ.get("PYTHON_CONFIG", "python3-config")
    compiler = shlex.split(os.environ.get("CC", "cc"))
    if not shutil.which(config) or not compiler or not shutil.which(compiler[0]):
        raise SystemExit("Requires a C compiler and CPython >=3.12 development files/python3-config.")
    includes = shlex.split(output([config, "--includes"]))
    links = shlex.split(output([config, "--embed", "--ldflags"]))
    build = ROOT / "build/python-embed"
    build.mkdir(parents=True, exist_ok=True)
    source = ROOT / "experiments/python-embed"
    command = compiler + ["-std=c11", "-Wall", "-Wextra", "-Werror", *includes,
                          str(source / "bridge.c"), str(source / "test_bridge.c"),
                          "-o", str(build / "test_bridge"), *links]
    print("Building optional C-only experiment:", shlex.join(command), flush=True)
    subprocess.run(command, check=True, timeout=120)
    subprocess.run([str(build / "test_bridge")], cwd=build, check=True, timeout=30)


if __name__ == "__main__":
    main()
