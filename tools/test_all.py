#!/usr/bin/env python3
"""Run the complete make test suite with bounded concurrency and separate logs."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time
import unittest

from test_units import ROOT, prepare_environment

# Keep all suites from the former sequential Makefile recipe. Long suites start
# first to avoid leaving a single expensive suite at the end of the run.
SUITES = (
    "javascript", "embedded",
    "cli", "json_iteration", "framing", "binary_count", "binary_iteration",
    "native", "native_pairs", "lsp_cost_audit", "lsp", "shared_globals",
    "bytes_native", "pattern_clauses", "binary_source", "composed_probe",
    "region", "construction", "native_forwarding", "io_cli",
    "binary_scalability", "binary_numbers", "binary_native", "json_oracle",
    "native_embedding", "native_embedding_generated",
    "binary_embedding", "binary_embedding_generated",
    "native_words", "std", "trust_inventory",
)


def cli_shards(count):
    """Partition discovered CLI cases exactly once, retaining unittest fixtures."""
    def cases(suite):
        for test in suite:
            if isinstance(test, unittest.TestSuite):
                yield from cases(test)
            else:
                yield test.id().removeprefix("test_cli.")
    names = list(cases(unittest.defaultTestLoader.loadTestsFromName("test_cli")))
    script = str(ROOT / "tools/test_cli.py")
    return [(f"cli-{index + 1}", [sys.executable, script, *names[index::count]])
            for index in range(min(count, len(names)))]


def integration_tasks(jobs):
    if jobs == 1:
        return [(name, None) for name in SUITES]
    cli = cli_shards(min(8, jobs * 2))
    other = [(name, None) for name in SUITES if name != "cli"]
    tasks = []
    # Interleave CLI batches and expensive integration suites so neither leaves
    # one long sequential tail while the other workers sit idle.
    while cli or other:
        if cli:
            tasks.append(cli.pop(0))
        if other:
            tasks.append(other.pop(0))
    return tasks


class Runner:
    def __init__(self, env, logs, timeout=900):
        self.env = env
        self.logs = Path(logs)
        self.logs.mkdir(parents=True, exist_ok=True)
        self.timeout = timeout
        self.lock = threading.Lock()
        self.active = set()
        self.stopped = False

    def cancel(self):
        with self.lock:
            self.stopped = True
            for process in self.active:
                self.kill(process)

    @staticmethod
    def kill(process):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def run(self, name, command=None):
        command = command or [sys.executable, str(ROOT / f"tools/test_{name}.py")]
        start = time.monotonic()
        log = self.logs / f"{name}.log"
        timed_out = False
        with log.open("w") as output:
            with self.lock:
                if self.stopped:
                    return dict(suite=name, seconds=0, returncode=130, timeout=False)
                process = subprocess.Popen(command, cwd=ROOT, env=self.env,
                    stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
                self.active.add(process)
            try:
                try:
                    code = process.wait(timeout=self.timeout)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    self.kill(process)
                    process.wait()
                    code = 124
            finally:
                with self.lock:
                    self.active.discard(process)
        elapsed = round(time.monotonic() - start, 2)
        status = "TIMEOUT" if timed_out else "PASS" if code == 0 else "FAIL"
        print(f"{status:7} {name:24} {elapsed:7.2f}s  {log}", flush=True)
        if code:
            print("\n".join(log.read_text(errors="replace").splitlines()[-30:]), flush=True)
        return dict(suite=name, seconds=elapsed, returncode=code, timeout=timed_out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    started = time.monotonic()
    print(f"Staging current Fibril package; then running suites with {args.jobs} workers", flush=True)
    env = prepare_environment(fresh=True)
    # All shared package writes finish before integration suites start. Unit
    # compilation remains incremental, and standalone suite entry points work.
    runner = Runner(env, ROOT / "build/test-logs")
    results = []
    pool = ThreadPoolExecutor(max_workers=args.jobs)
    try:
        results.append(runner.run("units"))
        if not results[0]["returncode"]:
            futures = [pool.submit(runner.run, name, command)
                       for name, command in integration_tasks(args.jobs)]
            for future in as_completed(futures):
                results.append(future.result())
    finally:
        runner.cancel()
        pool.shutdown(wait=True, cancel_futures=True)
        summary = dict(jobs=args.jobs, seconds=round(time.monotonic() - started, 2), results=results)
        (runner.logs / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    failed = [result["suite"] for result in results if result["returncode"]]
    print(f"{len(results)} suites in {summary['seconds']:.2f}s; {len(failed)} failed", flush=True)
    return bool(failed)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
