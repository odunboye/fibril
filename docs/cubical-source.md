# Experimental cubical `.fib` source

`fibril cubical-check PATH` loads a real UTF-8 `.fib` source file and invokes
`admitCanonicalCommonAbstraction` in the frozen
[CommonAdmission](common-admission.md) checker. This is a **separate experimental
source dialect**, intentionally parenthesized to make its small grammar explicit.
It is not ordinary Fibril syntax, production conversion, or executable code.
No ordinary command falls back to this dialect. Ordinary executable source now
has the separate, deliberately modest **constant-path regression guard** described
below; it does not change production conversion or introduce runtime paths.

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

## Ordinary executable `.fib`: checked constant-path regression guards

[policy-guard.fib](../examples/cubical/policy-guard.fib) is an ordinary executable
application, not input to `cubical-check`:

```fib
allow : (1 enabled : Bool) -> Bool
allow enabled = if enabled then True else False

reviewed : (1 enabled : Bool) -> Bool
reviewed enabled = if enabled then True else False

cubical policyStable : allow = reviewed by refl

requires policyStable
main : IO Unit
main = putStrLn (if allow True then "feature enabled" else "feature disabled")
```

```sh
make -j8 build
./build/exec/fibril check examples/cubical/policy-guard.fib
./build/exec/fibril run examples/cubical/policy-guard.fib
./build/exec/fibril emit-c examples/cubical/policy-guard.fib > /tmp/policy-guard.c
cc -std=c11 -I runtime/native /tmp/policy-guard.c runtime/native/fibril_runtime.c -o /tmp/policy-guard
/tmp/policy-guard
```

Both executions print `feature enabled`. Changing just one policy body rejects
normal checking/execution/emission. Changing both deliberately to the same
opposite policy succeeds and prints `feature disabled`. The baseline is a second
independently authored and checked definition, not an assumed path between two
arbitrary implementations. This is useful as a structural regression gate on a
reviewed pure policy; it does **not** prove that the reviewed policy is correct.
It adds no computational expressiveness and is much more modest than general
cubical application programming, algorithm equivalence, or transport.

### Exact syntax and binding

These are contextual declaration forms; `cubical` and `requires` remain legal
ordinary names when followed by their ordinary `:` signature. Each metadata line
starts in column 1 and occupies one line:

```text
cubical PROOF : LEFT = RIGHT by refl
requires PROOF
NAME : ordinary-type
NAME ... = ordinary-body
```

`LEFT` and `RIGHT` name **previous unrestricted ordinary definitions in the same
standalone file**. `PROOF` is an erased metadata label in the declaration-name
namespace, not a term or an assumption. Duplicate declaration names are rejected.
Ordinary uses of a proof label are rejected even when removing its metadata would
otherwise expose a same-spelled Prelude value; metadata cannot masquerade as a term.
Only `by refl` is supported; no user faces, dimensions, hypotheses, budgets,
certificates other than reflexivity, or proof-block fallback are accepted.
`requires PROOF` attaches to exactly the immediately following ordinary
signature/definition pair, not a block. Dangling/duplicate directives, unknown or
forward proof references, and attaching to other declaration forms are rejected.
The consumer's body must lexically reference the actual left endpoint declaration;
a same-spelled shadowing binder or a reference only in its signature is insufficient.
Every proof must have a later consumer. These checks establish an explicit source
connection, not a whole-program reachability or termination theorem for consumers.

### Checked source connection and soundness boundary

`Driver.Check.prepareSource` uses the normal declaration parser, lowering and
elaborator. Before returning the ordinary core program it invokes
`Cubical.Source.Application.checkConstantPaths`. For each endpoint separately:

1. Independently elaborate its declared type and body with **no global environment**,
   and check its declared type with the existing `inferRuntime`. The declaration
   must be unrestricted and ordinary. Recursion and references to other definitions,
   imports, or Prelude globals are not admitted as pure dependencies.
2. `Cubical.Source.PureDefinition.extractPure` constructs an intrinsically typed
   `Core.Quantitative.Syntax.Term` in the exact newest-first context, along with
   `CoreTranslation.Annotations` and an actual equality
   `coreTerm ty pureTerm annotations = originalCoreTerm`.
   `readPureType` similarly retains `coreType ty = originalCoreType`.
   This is exact re-embedding, not a Boolean assertion or equality of erasures.
3. Construct an actual `Uses pureTerm []` derivation. Quantities and all internal
   argument/binder obligations are retained; logical erasure does not restore
   erased or linear permissions. Linear and unrestricted arrows are supported;
   erased arrows/lambdas are deliberately rejected.
4. Locate the **actual declaration value and type** in the ordinary elaborated
   program using an indexed `DefinitionAt` let-spine derivation. Construct exact
   equalities from the independently checked closed type/value weakened into that
   actual local scope. This checks declaration identity and the contextual
   elaboration rather than trusting a matching source spelling.
5. Compare the two independent production images constructively, retaining source
   quantities, annotations, indices and every supported constructor. There is no
   beta/eta reduction, extensional equality, or production conversion expansion.
   Alpha-renamed binders are allowed because their resolved indices agree.
6. Generate `AdmissionTerm`s from those actual intrinsic terms. The total theorem
   `pureAdmissionShadow` proves their erasures equal the existing `commonTerm
   (shadowTerm term)`; `pureAdmissionTyped` preserves its actual logical context/type.
   Call the **unchanged** `admitCanonicalCommonAbstraction` with empty ordinary/path
   environments, `top`, independently generated left/right endpoints, the constant
   ordinary left body, and two `AERefl` boundary certificates. Its returned exact
   abstraction/boundary evidence is retained with the endpoint images while checking
   requirements. There are no named path assumptions, false-face shortcuts, runtime
   equality reflection, casts, or invented model-existence premises.

Supported images contain only Unit/Bool, nondependent arrows, variables, lambdas,
application, conditionals, and Unit elimination. Depth is capped at 64; generated
admission uses shared input/checking budgets 4096/1024 and zero solver calls.
Unsupported core constructors, dependent types, globals, recursion, effects,
resources, exhausted extraction/admission, or mismatching contextual values fail
closed. Ordinary let/ascription elaborations are accepted only when their **literal
lambda/application core trees** have this exact pure image and valid `Uses`; no
wrapper is stripped or normalized to obtain equality. The syntax image and common
shadow correspondence are proved, not a new operational adequacy theorem for the
entire production evaluator. No arbitrary production effect/resource semantics is
translated to the logical model.

Only metadata is erased, before ordinary checking/evaluation/emission. The existing
complete-program `inferRuntime`, ownership checks, effect planning and native
resource checks remain authoritative and unchanged. The same `prepareSource` gate
is used by `check` (including `--erased`/`--json`), `eval`, `run`, and standalone native
emission. Tests compare identical emitted C and evaluation reports with and without
valid metadata, as well as hosted/native output. There is no runtime proof value.

### Explicitly unsupported routes

This first integration is **standalone files only**. Module/import/package and
package-test checking explicitly reject metadata in any graph snapshot, including
an anonymous project entry or an imported dependency. There is no project bypass.
The legacy expression-only parser rejects metadata instead of lowering its internal
framing placeholders to Unit values. `elaborate`, `symbols`, `reference`,
`references`, `definition`, and `rename-preview` explicitly reject metadata
inspection; they must not display those placeholders as ordinary declarations or
propose incomplete proof-reference renames. `format` is supported: it preserves the
original metadata tokens and checks document shape including both metadata fields.
These tooling restrictions do not apply to ordinary files without metadata.

Run sequentially, without shared-cache installation:

```sh
make -j8 build
bash tools/test_cubical_worktree.sh
python3 tools/test_cubical_frontend.py
python3 tools/test_cubical_application.py
```
