# Experimental cubical `.fib` source

`fibril cubical-check PATH` loads a real UTF-8 `.fib` source file and invokes
`admitCanonicalCommonAbstraction` in the frozen
[CommonAdmission](common-admission.md) checker. This is a **separate experimental
source dialect**, intentionally parenthesized to make its small grammar explicit.
It is not ordinary Fibril syntax, production conversion, or executable code.
`check`, `eval`, `run`, imports, package checking and the production parser are
unchanged; none falls back to this dialect.

## Actual open path example

Run from the repository root after `make -j8 build`:

```sh
./build/exec/fibril cubical-check examples/cubical/open-path.fib
```

The tracked source is:

```text
(cubical
  (budget 4096 1024 16)
  (context (x Bool) (u Unit) (f (arrow Bool Bool)))
  (paths (p Bool x (if x False True)))
  (dimensions j)
  (abstract eta Bool top
    (ordinary x)
    (ordinary (if x False True))
    (lambda i (at p i))
    (endpoint p i 0)
    (endpoint p i 1)))
```

Actual output:

```text
Checked experimental cubical abstraction eta (zero and one boundaries).
Semantic provider conditional on CanonicalPathAdmissible for the checked declarations; no model existence or runtime execution claimed.
```

This checks the nonconstant **open** abstraction `λi. p i`, retaining the declared
ordinary endpoints `x` and `if x False True`. `p` is a hypothesis with those
endpoints, **not** a path definition, a manufactured Boolean-negation path, or
an existence assertion. No semantic model values or target proof are supplied
by the file. Admission independently checks both endpoints of every declaration,
the abstraction endpoints and body, and both boundary certificates under the
fresh zero/one faces. Its computational semantic provider works only given an
actual canonical semantic path environment satisfying `CanonicalPathAdmissible`
for exactly the checker-selected endpoint witnesses. Success does not construct
such an environment, assert its existence, execute the abstraction, or implement
transport. Source resource quantities/`Uses` are not part of this dialect.

## Exact grammar

One file contains exactly one `FILE` form. Parentheses are literal; `*` means
zero or more. Fixed tags and literals are case sensitive. Whitespace and `--`
line comments follow the existing lexer; layout has no meaning. `NAME` is an
ASCII identifier token (`[A-Za-z_][A-Za-z_0-9']*`) that is not a production lexer
keyword and is not `unit`. No strings, punctuation operators, implicit
application, infix arrows or other tokens/forms are accepted.

```text
FILE = (cubical (budget N N N)
          (context (NAME TYPE)*)
          (paths (NAME TYPE TERM TERM)*)
          (dimensions NAME*)
          (abstract NAME TYPE FACE PATH PATH
            (lambda NAME PATH) CERT CERT))
N    = decimal integer 0..4096 (1..4 digits)
TYPE = Unit | Bool | (arrow TYPE TYPE)
TERM = NAME | unit | True | False
     | (lam NAME TERM) | (app TYPE TERM TERM)
     | (if TERM TERM TERM) | (unitelim TERM TERM)
PATH = (ordinary TERM) | (at NAME INTERVAL)
     | (lam NAME PATH) | (app TYPE PATH PATH)
     | (if PATH PATH PATH) | (unitelim PATH PATH)
INTERVAL = 0 | 1 | NAME | (rev INTERVAL)
         | (meet INTERVAL INTERVAL) | (join INTERVAL INTERVAL)
FACE = top | bottom | (end NAME SIDE)
     | (and FACE FACE) | (or FACE FACE)
SIDE = 0 | 1
CERT = refl | (sym CERT) | (trans PATH CERT CERT)
     | (app TYPE CERT CERT) | (if CERT CERT CERT)
     | (unitelim CERT CERT)
     | (endpoint NAME INTERVAL SIDE) | (restrict FACE CERT)
```

The three budgets are shared input-node, checking-node, and solver-call
allowances respectively, not evaluation fuel. They are untrusted allowances;
annotations and certificates cannot bypass admission. Application `TYPE` is its
**domain** annotation; it is checked, not assumed. Lambda domains are obtained
from the expected nondependent arrow type. `unitelim` checks its first operand
at Unit and returns the type of its second operand. No reduction/conversion rule
or inference procedure is added. The abstract name is a report label, not a
new available path or global definition. Each file admits one abstraction.

Ordinary context, path names, and dimensions have **separate scopes**. The
leftmost declaration in each list receives index zero; duplicates within a list
are rejected. A spelling may occur in different scopes. Declaration endpoints
are ordinary terms, scoped over the entire ordinary context; they cannot use
path or dimension names. Ordinary variables occur only in `TERM`, path names
only in `at` and `endpoint`, dimensions only in intervals and `end`. An ordinary
`lam` adds a fresh index-zero ordinary binder and leaves path/dimension scopes
unchanged. Shadowing is lexical and capture avoiding. The abstraction's
`lambda` adds a fresh index-zero dimension **only** for its body and both
certificates. Its endpoints and ambient face use the older dimension scope.
Shadowing an older dimension does not capture it in weakened endpoints/faces:
CommonAdmission shifts the resolved older indices, not source spellings.
Unknown or escaped names are rejected before admission.

The last two certificates prove body equals the weakened left/right endpoint at
`ambient ∧ i=0` and `ambient ∧ i=1` respectively. `endpoint p r 0/1` requires
exactly `at p r` on the left and the corresponding **checked declared ordinary
endpoint** on the right, plus solver entailment of the requested endpoint under
the actual face. `refl` requires exact annotated syntax, not beta/eta equality.
Congruences require matching path constructors (an ordinary embedding cannot
stand in for path congruence). `trans` supplies an explicit middle path term.
`restrict SOURCE CERT` requires the target face to entail SOURCE, not the
reverse. There is no lambda equality certificate. A `bottom` ambient face is
allowed and may yield vacuous boundary entailments; a failed entailment is
rejected, not silently treated as a certificate.

## Bounds, errors and guarantees

Files are bounded to 16384 bytes before allocation/read using the existing
strict UTF-8/text loader; tokens are capped at 4096. The parenthesized reader
uses decreasing fuel 512 (including nested/sibling form traversal), and each
syntax resolver uses depth 64. These are frontend guards, not a combined
process-time/allocation theorem. CommonAdmission separately preflights all
scoped input and weakening reservations before proof construction, threads
shared allowances through both boundaries, and retains its fixed solver caps.
It has no runtime, conversion, or uncapped fallback.

IO/UTF-8/lexing/framing/scoping failures and admission failures return nonzero
exit status and stderr. Syntactic/scoping diagnostics include file/line/column;
checker failures point at the abstraction form and report `InputLimit`,
`CheckingLimit`, `SolverLimit`, `TypeMismatch`, `SyntaxMismatch`, or
`FaceMismatch`. The last includes false, incomplete, and capped solver checks;
rejection is not a proof of semantic inequality. Unsupported source features
fail closed. No general equality completeness, arbitrary dimension certificate
recertification, higher inductive types, dependent families, composition,
transport, path existence, production usage preservation, or runtime support is
claimed.

Validation (sequential, no shared-cache installation):

```sh
make -j8 build
bash tools/test_cubical_worktree.sh
python3 tools/test_cubical_frontend.py
```
