#!/usr/bin/env python3
"""Profile the pinned compiler in a separate cache; never clean the worktree build.

Use the same --cache for a second run to measure an unchanged rebuild.
Pack dependencies must already be installed (run make build once).
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shlex
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", type=Path,
                        help="isolated build directory (default: a new timestamped directory)")
    parser.add_argument("--typecheck", action="store_true")
    parser.add_argument("--compiler", type=Path,
                        help="compatible compiler executable (default: stock pinned compiler)")
    parser.add_argument("--timing", type=int, default=2,
                        help="Idris timing detail; use 3 for per-definition/termination timings")
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    cache = (args.cache or ROOT / "build/build-profiles" / stamp / "cache").resolve()
    if cache == ROOT / "build" or not cache.is_relative_to(ROOT / "build"):
        parser.error("--cache must be a separate directory inside this project's build directory")
    report_dir = ROOT / "build/build-profiles" / stamp
    report_dir.mkdir(parents=True)
    pack = shlex.split(os.environ.get("PACK", "pack"))

    def query(option):
        return subprocess.check_output(pack + ["--log-level=silence", option],
                                       cwd=ROOT, text=True).strip()

    env = os.environ.copy()
    compiler = str(args.compiler.resolve()) if args.compiler else subprocess.check_output(
        pack + ["--log-level=silence", "app-path", "idris2"], cwd=ROOT, text=True).strip()
    for variable, option in (("IDRIS2_PACKAGE_PATH", "package-path"),
                             ("IDRIS2_LIBS", "libs-path"), ("IDRIS2_DATA", "data-path")):
        env[variable] = query(option)
    command = [compiler, "--timing", str(args.timing), "--build-dir", str(cache),
               "--output-dir", str(cache / "exec"),
               "--typecheck" if args.typecheck else "--build", "fibril.ipkg"]
    cached_before = len(list(cache.rglob("*.ttc"))) if cache.exists() else 0
    source_hash = hashlib.sha256()
    inputs = [ROOT / "fibril.ipkg", ROOT / "pack.toml", *sorted((ROOT / "src").rglob("*.idr"))]
    for path in inputs:
        source_hash.update(str(path.relative_to(ROOT)).encode() + b"\0")
        source_hash.update(path.read_bytes() + b"\0")
    print(shlex.join(command), flush=True)
    print(f"Log: {report_dir / 'compiler.log'}", flush=True)
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    with (report_dir / "compiler.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    output = (report_dir / "compiler.log").read_text(errors="replace")
    modules = [{"source": source, "seconds": float(seconds)}
               for source, seconds in re.findall(
                   r"TIMING \+ Elaborating ([^\n]+): ([0-9.]+)s", output)]
    modules.sort(key=lambda row: row["seconds"], reverse=True)
    termination_checks = [{"function": name, "cpu_seconds": float(seconds)}
                          for name, seconds in re.findall(
                              r"TIMING \+\+\+ Checking Termination ([^\n]+): ([0-9.]+)s", output)]
    termination_checks.sort(key=lambda row: row["cpu_seconds"], reverse=True)
    report = {"command": command, "exit_code": result.returncode,
              "wall_seconds": elapsed, "cached_modules_before": cached_before,
              "child_user_cpu_seconds": cpu_after.ru_utime - cpu_before.ru_utime,
              "child_system_cpu_seconds": cpu_after.ru_stime - cpu_before.ru_stime,
              "peak_child_rss_bytes": cpu_after.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
              "peak_rss_scope": "maximum child RSS; includes Pack path-resolution children",
              "source_sha256": source_hash.hexdigest(),
              "source_tree_dirty": bool(subprocess.check_output(
                  ["git", "status", "--porcelain"], cwd=ROOT, text=True).strip()),
              "rebuilt_modules": len(modules), "module_timings": modules,
              "module_timing_clock": "compiler process CPU seconds (not wall time)",
              "slowest_termination_checks": termination_checks[:20],
              "incremental_backends": env.get("IDRIS2_INC_CGS", ""),
              "compiler_version": subprocess.check_output(
                  [compiler, "--version"], env=env, text=True).strip(),
              "revision": subprocess.check_output(
                  ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "note": "Nested compiler CPU timings overlap and exclude subprocess CPU time; wall_seconds measures elapsed build time."}
    (report_dir / "summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"{elapsed:.2f}s; exit {result.returncode}; {len(modules)} modules rebuilt")
    for row in modules[:15]:
        print(f"{row['seconds']:9.3f} CPU s  {row['source']}")
    print(f"Summary: {report_dir / 'summary.json'}")
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
