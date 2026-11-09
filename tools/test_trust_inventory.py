#!/usr/bin/env python3
"""Enforce the compiler's trust inventory: totality escapes are counted, never silent.

docs/guarantees.md claims "total by default". This test makes that checkable:
  * every src/Fibril module declares `%default total`;
  * no `partial`/`covering` declaration or unsafe primitive appears in the checking
    kernel directories (KERNEL);
  * outside the kernel, each file's escapes match BASELINE exactly, so a new escape
    hatch fails CI until someone adds it here on purpose, and a removed one is
    locked in. Run `python3 tools/test_trust_inventory.py --report` to print counts.
Comments are stripped before matching. This is a text scan, not a compiler check:
it cannot see escapes introduced through macros or other languages.
"""
from collections import Counter
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"

# Directories that implement checking, reduction, termination and elaboration.
KERNEL = ("Core", "Elaboration", "Termination", "Foundation", "Cubical", "Source", "Data", "Effect")

UNSAFE = re.compile(r"\b(assert_total|assert_smaller|believe_me|idris_crash|unsafePerformIO)\b")
PARTIAL = re.compile(r"^\s*(?:(?:public\s+)?export\s+)?(partial|covering)\b", re.M)
POLICY = re.compile(r"^\s*%default\s+(partial|covering)\b", re.M)

# path (relative to src/) -> Counter of escape kind. Edit deliberately, with review.
BASELINE = {
    # Hosted/stdio loops that run until input ends; not part of checking.
    "Fibril/Driver/Binary.idr": {"covering": 7},
    "Fibril/Driver/Binary/Count.idr": {"covering": 3},
    "Fibril/Driver/Interactive/Run.idr": {"covering": 2},
    "Fibril/Driver/Resource.idr": {"covering": 3},
    "Fibril/Runtime/ConsoleInput.idr": {"covering": 3},
    "Fibril/Runtime/InputOwnership.idr": {"covering": 1},
    "Fibril/Runtime/ScopedInput.idr": {"covering": 1},
    "Main.idr": {"covering": 1},
    # C backend: two assert_total calls, each justified at its call site as lowering
    # a term that contains only lambdas, pairs and variants.
    "Fibril/Driver/Native/Emit.idr": {"assert_total": 2},
}


def strip_comments(text):
    text = re.sub(r"\{-.*?-\}", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


def inventory():
    found = {}
    for path in sorted(SRC.rglob("*.idr")):
        text = strip_comments(path.read_text(encoding="utf-8"))
        counts = Counter(m.group(1) for m in UNSAFE.finditer(text))
        counts.update(m.group(1) for m in PARTIAL.finditer(text))
        counts.update("%default " + m.group(1) for m in POLICY.finditer(text))
        if counts:
            found[str(path.relative_to(SRC))] = counts
    return found


def in_kernel(relative):
    parts = Path(relative).parts
    return len(parts) > 2 and parts[0] == "Fibril" and parts[1] in KERNEL


class TrustInventory(unittest.TestCase):
    def test_every_module_declares_default_total(self):
        missing = [str(p.relative_to(SRC)) for p in sorted((SRC / "Fibril").rglob("*.idr"))
                   if not re.search(r"^%default\s+total\b", p.read_text(encoding="utf-8"), re.M)]
        self.assertEqual(missing, [], "modules without %default total")

    def test_kernel_has_no_totality_or_safety_escapes(self):
        escapes = {path: dict(counts) for path, counts in inventory().items() if in_kernel(path)}
        self.assertEqual(escapes, {}, "kernel modules must stay total and free of unsafe primitives")
        self.assertEqual([path for path in BASELINE if in_kernel(path)], [],
                         "the baseline must not whitelist kernel modules")

    def test_remaining_escapes_match_the_baseline(self):
        actual = {path: dict(counts) for path, counts in inventory().items()}
        expected = {path: dict(counts) for path, counts in BASELINE.items()}
        self.assertEqual(actual, expected,
                         "escape inventory changed: review each new escape, then update BASELINE "
                         "(and docs/guarantees.md if the trust story changes)")

    def test_scanner_sees_what_it_claims_to(self):
        # Guard against a regex that silently matches nothing.
        sample = "partial\nfoo : Nat\n-- assert_total in a comment\nbar = assert_total baz\n{- believe_me -}\n"
        text = strip_comments(sample)
        self.assertEqual([m.group(1) for m in PARTIAL.finditer(text)], ["partial"])
        self.assertEqual([m.group(1) for m in UNSAFE.finditer(text)], ["assert_total"])


if __name__ == "__main__":
    if "--report" in sys.argv:
        for path, counts in inventory().items():
            print(f"{path}: {dict(counts)}")
        sys.exit(0)
    unittest.main()
