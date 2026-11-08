#!/usr/bin/env python3
"""End-to-end tests of the isolated CommonAdmission .fib frontend (no installs)."""
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / "build/exec/fibril"
EXAMPLE = ROOT / "examples/cubical/open-path.fib"
SOURCE = EXAMPLE.read_text()
CHECKED = "Checked experimental cubical abstraction eta (zero and one boundaries)."
CONDITIONAL = "Semantic provider conditional on CanonicalPathAdmissible"


def invoke(path, command="cubical-check"):
    return subprocess.run([str(CLI), command, str(path)], cwd=ROOT,
                          text=True, capture_output=True, timeout=30)


def main():
    count = 0
    with tempfile.TemporaryDirectory(prefix="fibril-cubical-source-") as temp:
        path = Path(temp) / "case.fib"

        def check(label, source, diagnostic=None):
            nonlocal count
            path.write_text(source)
            result = invoke(path)
            if diagnostic is None:
                assert result.returncode == 0, (label, result.stdout, result.stderr)
                assert result.stdout.startswith(CHECKED + "\n"), (label, result.stdout)
                assert CONDITIONAL in result.stdout, (label, result.stdout)
                assert not result.stderr, (label, result.stderr)
            else:
                assert result.returncode != 0, (label, result.stdout)
                assert diagnostic in result.stderr, (label, result.stderr)
                assert "Checked experimental" not in result.stdout, (label, result.stdout)
                assert str(path) + ":" in result.stderr, (label, result.stderr)
            count += 1

        # Real tracked source, not a generated Idris observer.
        result = invoke(EXAMPLE)
        assert result.returncode == 0 and CHECKED in result.stdout, result
        assert CONDITIONAL in result.stdout
        count += 1
        check("both boundaries", SOURCE)
        check("ordinary endpoint unknown", SOURCE.replace("(ordinary x)", "(ordinary missing)"),
              "unknown ordinary name: missing")
        check("path unknown", SOURCE.replace("(at p i)", "(at missing i)"), "unknown path name: missing")
        check("dimension unknown", SOURCE.replace("(at p i)", "(at p missing)"), "unknown dimension name: missing")
        check("wrong zero endpoint", SOURCE.replace("(ordinary x)", "(ordinary True)"), "SyntaxMismatch")
        check("wrong one endpoint", SOURCE.replace("(ordinary (if x False True))", "(ordinary False)"), "SyntaxMismatch")
        check("wrong declaration endpoint type", SOURCE.replace("(p Bool x", "(p Unit x"), "TypeMismatch")
        check("wrong expected type", SOURCE.replace("(abstract eta Bool", "(abstract eta Unit"), "TypeMismatch")
        check("wrong second boundary certificate", SOURCE.replace("(endpoint p i 1)", "(endpoint p i 0)"), "SyntaxMismatch")
        check("escaped fresh dimension", SOURCE.replace("(ordinary x)", "(at p i)"), "unknown dimension name: i")
        # Correct syntax/name/type; solver rejects a genuinely false entailment.
        check("false face entailment", SOURCE.replace("(at p i)", "(at p j)")
              .replace("(endpoint p i", "(endpoint p j"), "FaceMismatch")
        check("false restriction", SOURCE.replace("(endpoint p i 0)",
              "(restrict (end j 0) (endpoint p i 0))"), "FaceMismatch")
        check("input exhausted", SOURCE.replace("4096 1024 16", "0 1024 16"), "InputLimit")
        check("checking exhausted", SOURCE.replace("4096 1024 16", "4096 0 16"), "CheckingLimit")
        check("second solver call exhausted", SOURCE.replace("4096 1024 16", "4096 1024 1"), "SolverLimit")
        check("unsupported transport", SOURCE.replace("(at p i)", "(transport p i)"), "unsupported path term form")
        check("unsupported type", SOURCE.replace("(x Bool)", "(x Type)"), "unsupported type")
        check("unsupported ordinary recursion", SOURCE.replace("(ordinary x)", "(ordinary (fix x))"), "unsupported ordinary form")
        check("trailing syntax", SOURCE + "\n(unit)", "unexpected trailing source")
        check("unterminated source", SOURCE.rstrip()[:-1], "missing closing parenthesis")
        check("duplicate ordinary", SOURCE.replace("(x Bool)", "(x Bool) (x Unit)"), "duplicate ordinary")
        check("duplicate path", SOURCE.replace("(paths", "(paths (p Bool True False)"), "duplicate path")
        check("duplicate dimension", SOURCE.replace("(dimensions j)", "(dimensions j j)"), "duplicate dimension")
        check("budget cap", SOURCE.replace("4096 1024 16", "4097 1024 16"), "budget must be 0..4096")
        check("token cap", SOURCE + " x" * 4096, "token limit (4096)")
        check("file cap", " " * 16385, "16384-byte read limit")
        check("lexical diagnostic", SOURCE.replace("(at p i)", "(at p @)"), "Unexpected character")
        check("parser depth cap", "(" * 300 + "unit" + ")" * 300, "source form limit exhausted")
        check("scoper depth cap", SOURCE.replace("(ordinary x)",
              "(ordinary " + "(lam a " * 70 + "x" + ")" * 70 + ")"), "term depth exhausted")
        check("restricted certificate", SOURCE.replace("(endpoint p i 0)",
              "(restrict top (restrict (end i 0) (endpoint p i 0)))"), "FaceMismatch")
        check("valid restriction", SOURCE.replace("(endpoint p i 0)",
              "(restrict (end i 0) (endpoint p i 0))"))
        check("ambient restriction", SOURCE.replace("eta Bool top", "eta Bool (end j 0)"))
        check("nonzero term and path lookup", SOURCE.replace("(context", "(context (unused Unit)")
              .replace("(paths", "(paths (unused Unit unit unit)"))
        check("separate namespaces", SOURCE.replace("(context (x Bool)", "(context (p Unit) (i Unit) (x Bool)"))
        # The fresh binder shadows an older dimension; weakening still refers to
        # the old dimension in the ambient face, not the freshly bound index.
        check("dimension shadowing", SOURCE.replace("(dimensions j)", "(dimensions i)")
              .replace("eta Bool top", "eta Bool (end i 1)"))
        arrow = """(cubical (budget 4096 1024 16)
          (context (x Bool) (u Unit))
          (paths (p (arrow Unit Bool) (lam u x) (lam u (if x False True))))
          (dimensions)
          (abstract eta (arrow Unit Bool) top
            (ordinary (lam u x)) (ordinary (lam u (if x False True)))
            (lambda i (at p i)) (endpoint p i 0) (endpoint p i 1)))"""
        check("arrow endpoints capture ordinary context", arrow)
        check("ordinary binder shadows wrong context type", arrow.replace("(lam u x)", "(lam x x)"), "TypeMismatch")
        # A closed constant abstraction also exercises ordinary application,
        # Unit elimination and lambda shadowing, with checked annotations.
        term = "(unitelim unit (app Unit (lam x x) unit))"
        constant = f"""(cubical (budget 4096 1024 0)
          (context (x Bool)) (paths) (dimensions)
          (abstract eta Unit top (ordinary {term}) (ordinary {term})
            (lambda i (ordinary {term})) refl refl))"""
        check("Unit arrow application and capture avoidance", constant)
        check("untrusted application annotation", constant.replace("app Unit", "app Bool"), "TypeMismatch")
        check("certificate symmetry", constant.replace("refl refl", "(sym refl) refl"))
        check("certificate transitivity", constant.replace("refl refl", f"(trans (ordinary {term}) refl refl) refl"))
        def reflexive_path(ty, term, cert="refl"):
            return f"""(cubical (budget 4096 1024 16)
              (context (x Bool)) (paths (p Bool x (if x False True)))
              (dimensions k j)
              (abstract eta {ty} (or (end k 0) (and (end j 0) top))
                {term} {term} (lambda i {term}) {cert} {cert}))"""

        check("path binder does not capture named path or old dimension",
              reflexive_path("(arrow Unit Bool)", "(lam p (at p j))"))
        check("path binder leaves ordinary context accessible",
              reflexive_path("(arrow Unit Bool)", "(lam a (ordinary x))"))
        check("interval constructors and weakened nonzero dimensions",
              reflexive_path("Bool", "(at p (join (meet k (rev j)) j))"))
        check("path application congruence", reflexive_path("Unit",
              "(app Unit (lam a (ordinary a)) (ordinary unit))", "(app Unit refl refl)"))
        check("path conditional congruence", reflexive_path("Unit",
              "(if (ordinary x) (ordinary unit) (ordinary unit))", "(if refl refl refl)"))
        check("path unit elimination congruence", reflexive_path("Unit",
              "(unitelim (ordinary unit) (ordinary unit))", "(unitelim refl refl)"))
        check("wrong certificate congruence domain", reflexive_path("Unit",
              "(app Unit (lam a (ordinary a)) (ordinary unit))", "(app Bool refl refl)"), "TypeMismatch")
        # Ordinary production parsing has no fallback to this dialect.
        path.write_text(SOURCE)
        result = invoke(path, "check")
        assert result.returncode != 0 and "Checked experimental" not in result.stdout, result
        count += 1
        result = invoke(Path(temp) / "absent.fib")
        assert result.returncode != 0 and "Source file IO error" in result.stderr, result
        count += 1
    print(f"Cubical frontend CLI: {count} end-to-end cases passed.")


if __name__ == "__main__":
    main()
