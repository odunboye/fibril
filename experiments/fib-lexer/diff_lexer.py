#!/usr/bin/env python3
"""Differential test: the Fibril-written lexer (native C) against `fibril lex-source`.

Usage: diff_lexer.py [--fibril PATH] [--keep DIR] FILE_OR_DIR...

Builds src/Main.fib with emit-c-binary, then for each .fib file compares
(start, end, kind) token triples. A file with a sibling FILE.expected is instead compared to
this lexer's exact stdout (for inputs the reference lexer rejects).

Exit status is nonzero on any mismatch, native budget failure or crash, or if nothing was
compared; --allow-partial accepts budget failures. The stock runtime stops after 100000
steps, so use --raise-budgets (private copy of the runtime with larger caps) for real files. The Idris lexer reports scalar line:col, converted here to
byte offsets. Files the Idris lexer rejects, and files over the 4096-byte chunk, are skipped
and counted; a native budget failure is reported separately from a real mismatch.
"""
import argparse, pathlib, re, shutil, subprocess, sys, tempfile

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[1]  # worktree root: runtime/native
CAP = 4096


def raised_runtime(out):
    """Copy of runtime/native with the step, depth and allocation caps lifted (measurement only)."""
    dst = out / "runtime-raised"
    shutil.copytree(ROOT / "runtime/native", dst, dirs_exist_ok=True)
    c = dst / "fibril_runtime.c"
    text = c.read_text()
    for old, new in [("#define F_MAX_STEPS ((size_t)100000)", "#define F_MAX_STEPS ((size_t)2000000000)"),
                     ("#define F_MAX_DEPTH ((size_t)512)", "#define F_MAX_DEPTH ((size_t)1000000)"),
                     ("#define F_MAX_BYTES ((size_t)16777216)", "#define F_MAX_BYTES ((size_t)8589934592ULL)")]:
        if old not in text:
            sys.exit(f"runtime changed: {old} not found")
        text = text.replace(old, new)
    c.write_text(text)
    return dst


def build(fibril, out, runtime):
    c = out / "lex.c"
    with open(c, "w") as f:
        subprocess.run([fibril, "emit-c-binary", "--source-dir", str(HERE / "src"), str(HERE / "src/Main.fib")],
                       stdout=f, check=True)
    exe = out / "lex"
    rt = pathlib.Path(runtime) if runtime else ROOT / "runtime/native"
    subprocess.run(["cc", "-std=c11", "-O1", "-I", str(rt), str(c), str(rt / "fibril_binary_runtime.c"), "-o", str(exe)],
                   check=True)
    return exe


TOKEN = re.compile(r'^(\d+):(\d+)-(\d+):(\d+) (\S+) ')


def reference(fibril, path, data):
    """(start, end, kind) triples from the Idris lexer, in byte offsets; None if it rejects."""
    p = subprocess.run([fibril, "lex-source", str(path)], capture_output=True)
    if p.returncode != 0:
        return None
    text = data.decode("utf-8")
    line_start = [0]  # scalar index of each line start
    for i, ch in enumerate(text):
        if ch == "\n":
            line_start.append(i + 1)
    # CRLF counts as one position step in the Idris lexer; keep this simple and skip such files.
    byte_at = [0]
    for ch in text:
        byte_at.append(byte_at[-1] + len(ch.encode("utf-8")))

    def off(line, col):
        return byte_at[line_start[line - 1] + col - 1]

    out = []
    for raw in p.stdout.decode("utf-8").splitlines():
        m = TOKEN.match(raw)
        if m:
            l1, c1, l2, c2, kind = m.groups()
            out.append((off(int(l1), int(c1)), off(int(l2), int(c2)), kind))
    return out


def mine(exe, data):
    p = subprocess.run([str(exe)], input=data, capture_output=True)
    if p.returncode != 0:
        return None, p.stderr.decode(errors="replace").strip() or f"exit {p.returncode}"
    if p.stdout.endswith(b"input exceeds 4096 bytes\n"):
        return None, "truncated"
    toks = []
    for raw in p.stdout.decode("utf-8").splitlines():
        m = re.match(r"^(\d+)-(\d+) (.+)$", raw)
        if m:
            toks.append((int(m[1]), int(m[2]), m[3]))
        else:
            toks.append(("error", raw))
    return toks, None


def collapse(tokens, data):
    """The Idris lexer folds `(op)` written without spaces into one name token; do the same."""
    out, i = [], 0
    while i < len(tokens):
        t = tokens[i]
        if (i + 2 < len(tokens) and all(len(x) == 3 for x in tokens[i:i + 3]) and t[2] == "(" and
                tokens[i + 1][2] == "operator" and tokens[i + 2][2] == ")" and
                t[1] == tokens[i + 1][0] and tokens[i + 1][1] == tokens[i + 2][0]):
            out.append((t[0], tokens[i + 2][1], "name"))
            i += 3
        else:
            out.append(t)
            i += 1
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fibril", default=str(ROOT / "build/exec/fibril"))
    ap.add_argument("--keep")
    ap.add_argument("--runtime", help="directory of C runtime sources (default: runtime/native; the stock runtime stops after 100000 steps)")
    ap.add_argument("--raise-budgets", action="store_true", help="build against a copy of the runtime with the caps lifted")
    ap.add_argument("--allow-partial", action="store_true", help="exit 0 even if some files hit a native budget")
    ap.add_argument("paths", nargs="+")
    args = ap.parse_args()
    files = []
    for p in map(pathlib.Path, args.paths):
        files += sorted(p.rglob("*.fib")) if p.is_dir() else [p]
    tmp = pathlib.Path(args.keep) if args.keep else pathlib.Path(tempfile.mkdtemp())
    tmp.mkdir(parents=True, exist_ok=True)
    if args.raise_budgets and not args.runtime:
        args.runtime = str(raised_runtime(tmp))
    exe = build(args.fibril, tmp, args.runtime)
    counts = dict(match=0, mismatch=0, rejected=0, too_big=0, budget=0, crash=0)
    for path in files:
        data = path.read_bytes()
        expected = path.with_suffix(".expected")
        if expected.exists():
            p = subprocess.run([str(exe)], input=data, capture_output=True)
            if p.returncode == 0 and p.stdout == expected.read_bytes():
                counts["match"] += 1
            else:
                counts["mismatch"] += 1
                print(f"MISMATCH {path}: expected {expected.read_bytes()!r}, got {p.stdout!r} (rc={p.returncode})")
            continue
        if len(data) > CAP:
            counts["too_big"] += 1
            continue
        if b"\r" in data:
            counts["rejected"] += 1
            continue
        ref = reference(args.fibril, path, data)
        if ref is None:
            counts["rejected"] += 1
            continue
        got, err = mine(exe, data)
        if got is None:
            kind = "budget" if "budget" in err else "crash"
            counts[kind] += 1
            print(f"{kind.upper():8} {path}: {err[:100]}")
            continue
        got = collapse(got, data)
        if got == ref:
            counts["match"] += 1
        else:
            counts["mismatch"] += 1
            n = next((i for i, (a, b) in enumerate(zip(got, ref)) if a != b), min(len(got), len(ref)))
            print(f"MISMATCH {path}: token {n}: mine={got[n] if n < len(got) else None} ref={ref[n] if n < len(ref) else None}")
    print(counts)
    bad = counts["mismatch"] or counts["crash"] or (counts["budget"] and not args.allow_partial)
    return 1 if bad or counts["match"] == 0 else 0


if __name__ == "__main__":
    sys.exit(main())
