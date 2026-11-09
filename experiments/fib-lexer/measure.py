#!/usr/bin/env python3
"""Measure the Fibril lexer's resource use with the runtime's FIBRIL_STATS line.

Usage: measure.py [--fibril PATH] [--src DIR] FILE...

Builds src/Main.fib against runtime/native with the caps lifted by -DF_MAX_* (so a run that would
exceed the stock limits still reports what it needed), then runs each FILE and prints steps,
peak depth and allocated bytes. Startup (empty input) is measured separately so driver overhead
does not hide lexer cost; the per-byte columns subtract it.
"""
import argparse, pathlib, re, subprocess, sys, tempfile, os

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STATS = re.compile(rb"fibril stats: steps=(\d+) peak_depth=(\d+) bytes=(\d+)")


RAISED = ["-DF_MAX_STEPS=((size_t)2000000000)", "-DF_MAX_DEPTH=((size_t)1000000)",
          "-DF_MAX_BYTES=((size_t)8589934592ULL)"]


def build(fibril, src, out):
    with open(out / "lex.c", "w") as f:
        subprocess.run([fibril, "emit-c-binary", "--source-dir", str(src), str(src / "Main.fib")], stdout=f, check=True)
    exe = out / "lex"
    rt = ROOT / "runtime/native"
    subprocess.run(["cc", "-std=c11", "-O1", *RAISED, "-I", str(rt), str(out / "lex.c"), str(rt / "fibril_binary_runtime.c"), "-o", str(exe)], check=True)
    return exe


def run(exe, data):
    p = subprocess.run([str(exe)], input=data, capture_output=True, env={**os.environ, "FIBRIL_STATS": "1"})
    m = STATS.search(p.stderr)
    if p.returncode != 0 or not m:
        return None
    return tuple(int(x) for x in m.groups())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fibril", default=str(ROOT / "build/exec/fibril"))
    ap.add_argument("--src", default=str(HERE / "src"))
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()
    with tempfile.TemporaryDirectory() as d:
        exe = build(args.fibril, pathlib.Path(args.src), pathlib.Path(d))
        base = run(exe, b"")
        print(f"startup (empty input): steps={base[0]} peak_depth={base[1]} bytes={base[2]}")
        tot = [0, 0, 0]
        print(f"{'file':44} {'bytes':>6} {'steps/B':>8} {'depth/B':>8} {'alloc/B':>9}")
        for name in args.files:
            data = pathlib.Path(name).read_bytes()
            got = run(exe, data)
            if got is None:
                print(f"{name:44} {len(data):6} FAILED")
                continue
            n = len(data)
            print(f"{pathlib.Path(name).name:44} {n:6} {(got[0]-base[0])/n:8.1f} {(got[1]-base[1])/n:8.2f} {(got[2]-base[2])/n:9.0f}")
            for i in range(3):
                tot[i] += got[i] - base[i]
            tot.append(n) if len(tot) == 3 else tot.__setitem__(3, tot[3] + n)
        if len(tot) > 3 and tot[3]:
            print(f"{'TOTAL (startup removed)':44} {tot[3]:6} {tot[0]/tot[3]:8.1f} {tot[1]/tot[3]:8.2f} {tot[2]/tot[3]:9.0f}")


if __name__ == "__main__":
    sys.exit(main())
