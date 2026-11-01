#!/usr/bin/env python3
"""Run fixed, validated workloads; persist raw samples and environment metadata."""
import argparse
from datetime import datetime, timezone
import json
import hashlib
from pathlib import Path
import platform
import statistics
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CASES = ("substitution", "reduction", "erased", "runtime", "interval", "face", "expose-full", "expose-head")


def command(*args):
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True,
                          check=True, timeout=120).stdout.strip()


def measure(executable, case, size, iterations):
    output = command(str(executable), case, str(size), str(iterations))
    fields = dict(line.split("=", 1) for line in output.splitlines())
    if int(fields["passed"]) != iterations:
        raise RuntimeError(f"Invalid checksum: {output}")
    elapsed = int(fields["elapsed_ns"])
    if elapsed < 0:
        raise RuntimeError("Negative monotonic duration")
    return elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="Smoke run, not a performance baseline")
    parser.add_argument("--output", type=Path, default=ROOT / "build/benchmarks/latest.json")
    args = parser.parse_args()
    samples, warmups, iterations = (1, 1, 1) if args.quick else (5, 1, 10)
    sizes = (2,) if args.quick else (2, 4, 6)
    # Build is deliberately outside measured workload durations.
    command("pack", "--cg=chez", "build", "fibril-bench")
    executable = ROOT / "bench/build/exec/fibril-bench"
    results = []
    for case in CASES:
        for size in sizes:
            for _ in range(warmups):
                measure(executable, case, size, iterations)
            times = [measure(executable, case, size, iterations) for _ in range(samples)]
            median = statistics.median(times)
            results.append({"workload": case, "size": size, "iterations": iterations,
                            "raw_batch_ns": times, "median_batch_ns": median,
                            "median_ns_per_iteration": median / iterations})
            print(f"{case:14} size={size} median={median / iterations:.0f} ns/iteration")
    report = {
        "schema": 1, "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "revision": command("git", "rev-parse", "HEAD"),
        "working_tree_status": command("git", "status", "--porcelain"),
        "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in sorted(ROOT.rglob("*"))
                          if path.is_file() and "build" not in path.relative_to(ROOT).parts
                          and ".git" not in path.relative_to(ROOT).parts
                          and (path.suffix in (".idr", ".ipkg") or path.name in ("pack.toml", "benchmark.py"))},
        "platform": platform.platform(), "machine": platform.machine(),
        "processor": platform.processor(), "python": platform.python_version(),
        "pack_info": command("pack", "info"),
        "code_generator": "chez", "sizes": sizes, "samples": samples,
        "warmup_processes_per_case": warmups, "quick": args.quick,
        "measurement": "In-process monotonic batch duration including construction, validation, and checksum output; excludes process startup and build.",
        "limitations": "Fresh process for each sample/warmup; no steady-state in-process warmup, GC control, allocation/RSS metrics, or regression thresholds.",
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Report: {args.output}")


if __name__ == "__main__":
    main()
