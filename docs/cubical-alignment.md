# Cubical alignment: first checked path milestone

**Status: roadmap, not an implemented path calculus or a soundness claim.**
Fibril's target remains a practical, resource-aware language with a De Morgan
cubical foundation suitable for HoTT. Its ordinary checker, runtime, recursive
fragments, imports, and C emitter are experimental infrastructure; none by
itself supplies cubical equality, transport, univalence, or higher inductive
types.

The initial mathematical reference is [CCHM 2018](foundation-baseline.md).
The exact quantitative extension and its interaction with Fibril's existing
features remain to be specified. The existing interval/face implementation is
useful infrastructure, not a certificate that the complete calculus or its
quantitative extension is sound.

## Next vertical slice

The next foundation milestone is **a checked, computational path example**:
the implementation should construct a simple path, apply it at both interval
endpoints, check the expected boundaries, and reduce the applications to the
corresponding endpoint values. This is an internal milestone first; surface
syntax and backend support are not prerequisites for claiming that the internal
example works. It is deliberately smaller than univalence or a full HoTT
implementation.

Before implementing the slice:

1. Cite the exact CCHM rules adopted for contexts, path formation, abstraction,
   application, boundaries and computation, including any restrictions. State
   what is postponed; do not silently invent a hybrid calculus.
2. Define how computational variables, dimension variables, face assumptions,
   and universe levels interact. Dimension substitution is not ordinary term
   substitution. State how checked boundaries use the existing face machinery.
3. Specify the interaction with quantities, including what is consumed when a
   boundary is checked, substitution through linear contexts, and whether any
   path data or operation survives runtime erasure. If these rules are not
   justified, keep the slice out of trusted checking rather than silently assuming
   Idris-style rules carry over.
4. Define the conversion and reduction rules, resource budgets, and behavior
   on exhaustion. A failed or inconclusive boundary check must not be accepted.
   Distinguish definitional equality, paths, and Boolean equality.
5. Specify how partial/recursive definitions and existing inductive forms enter
   types and proofs. Do not claim totality, consistency, or termination beyond
   the fragment actually checked.

## Candidate first fragment (not implemented)

As preliminary infrastructure, `src/Fibril/Foundation/DeMorgan/PathSyntax.idr`
contains an isolated toy syntax and capture-avoiding dimension substitution,
with regression checks in `test/src/Tests/Main.idr`. It is not connected to the
core checker, does not represent path types, and accepts unchecked syntax; it
is not the checked-path milestone. `src/Fibril/Foundation/DeMorgan/ClosedPath.idr`
adds a separate, fuel-bounded experiment checking only literal constant Boolean
paths and their literal endpoint applications. Its Booleans are Idris-level
placeholders, not independently checked Fibril terms. It rejects other forms,
including interval expressions equivalent to endpoints, and is not integrated
into the core checker. Tests in `test/src/Tests/Main.idr` exercise both endpoints,
boundary mismatch, unsupported forms and budget exhaustion. This narrow experiment
is not yet the milestone's independently checked Fibril path.
`ClosedCorePath.idr` additionally bridges a closed core Boolean fragment to that
experiment: literals and `BoolCase` expressions composed entirely from that
fragment. It independently checks the body and endpoints with `checkErased`,
compares them with bounded ordinary beta conversion, and returns the checked
body for either endpoint. Conversion is restricted to the admitted Boolean
grammar; it is not general cubical conversion. Unsupported syntax is rejected
even in dead branches. This is a narrow helper, not a path constructor or
judgment in the core checker; checker depth, reduction and toy-path budgets are
per-call limits, with the reduction budget reused independently for each core
check and normalization rather than acting as a shared global budget. Its
`CorePathExpr` supplies separate dimension-scoped raw abstraction and
application constructors, capture-avoiding dimension substitution, and
`runCorePathExpr`, which evaluates closed De Morgan interval expressions with
a depth limit and checks the path before instantiating its dimension binder.
Closed intervals have no generators and therefore reduce to an endpoint; this
does not decide equality of open intervals. Embedded core terms remain closed;
scoping raw syntax is not evidence of typing. `applyCorePathAt` also performs a
checked beta step for this constant-path fragment at an open scoped interval;
it does not decide interval equality or support neutral paths. Core-checker
integration remains unsupported. Interval evaluation and path checking reuse
the remaining path fuel independently. The experimental body grammar also
allows nested applications of syntactic constant paths, including at bound
dimensions; their inferred endpoints coincide. Body traversal has a separate
depth limit, and this still does not admit genuinely varying paths.

The ordinary, non-dependent path rules in [CCHM §3.1, Figure 2](https://arxiv.org/html/1611.02108#S3.SS1) are the reference for this slice. In their notation, `Path A a b` is formed when `A` is a type and both endpoints have type `A`; if `t : A` in a context extended by a fresh dimension `i`, then `<i> t : Path A t[i:=0] t[i:=1]`. If `p : Path A a b` and `r` is an interval expression, then `p r : A`. The stated equalities include `(<i> t) r = t[i:=r]` and, even for a neutral `p`, `p 0 = a` and `p 1 = b`. Figure 2 also gives path eta; it is **not** required for this initial fragment. Dependent paths from CCHM §9.2 are postponed.

To avoid making unsupported quantitative assumptions, the first candidate is a **separate, internal, closed fragment**: no computational variables, global definitions, recursion, effects, or runtime emission. Permit dimension variables and dimension substitution, but initially no face-restricted contexts, systems, composition, or transport. Choose a closed base type and closed values already independently checked by a terminating fragment; do not assume arbitrary existing core definitions are safe. The first example is the constant path `<i> a : Path A a a`, with both applications reducing to `a`. A boundary mismatch must be rejected, not converted into an axiom.

This restriction avoids deciding how a path captures or duplicates a linear resource; it is **not** a quantitative path rule. Path construction and endpoint checking are compile-time operations in this experiment, with no assertion yet about general erasure. Before integration with the ordinary checker, specify how quantities, substitution, conversion and runtime representation compose, and justify those rules against a selected quantitative calculus. Nor does a separately checked closed example establish consistency of the existing language.

Implementation must retain separate computational and dimension scopes, use capture-avoiding dimension substitution under binders, and check the body and both endpoint equalities rather than trusting annotations. Conversion must distinguish success, mismatch and exhaustion; exhaustion rejects the check. Endpoint equality for neutral paths is a typed rule, not an untyped rewrite based on an unverified annotation. General face-restricted conversion and path eta remain outside this candidate; rejecting otherwise valid CCHM terms is acceptable for this fragment.

## Testing this worktree

While this experiment is uncommitted, Pack can select an installed Fibril
package from the shared cache that does not contain the worktree's new modules.
Run `tools/test_cubical_worktree.sh` from the repository root to build this
worktree and run the Idris test suite against a temporary package containing
its compiled modules. The script does not overwrite Pack's shared package
cache; it also verifies that an external module cannot construct the opaque
checked-path witness. It does not run the CLI or native test suites. Avoid concurrent builds
that write to the same worktree. This is a worktree-testing workaround, not a
fix to Pack's cache selection.

## Prototype review and next implementation gate

The current experiment is useful for exercising dimension scopes, nested
substitution, endpoint applications, and fail-closed rejection. Its closed core
Boolean grammar excludes computational captures, recursive definitions and
effects. Retain these tests and the use of the ordinary erased checker.

It is **not yet the independent path judgment** described above:

1. `CorePathExpr` is separate raw syntax, not a core type former. The isolated
   `IndependentPath` module exposes an opaque `CheckedClosedPath` witness only
   after the fragment checker accepts, but this is not a core typing derivation.
   `checkCorePathExpr` itself returns only a status; callers must not treat raw
   `CoreStepped` syntax as a reusable typing certificate. Witness construction
   distinguishes rejection from exhaustion with `ClosedPathFailure`, whose
   constructors cannot express success. Applying a witness rechecks its recorded
   inputs under the supplied budgets.
2. `collapseBody` accepts nested syntactic constant paths by inferring identical
   endpoints, then discards their dimension applications. This is a deliberately
   narrow shortcut, not general path inference, face checking, or conversion.
   The current checker explicitly substitutes both endpoints, then uses the
   ordinary bounded beta comparison on admitted Boolean expressions, not
   general cubical conversion; both faces remain constant by construction.
3. Checking depth, reduction fuel, path depth, and interval depth are reused in
   separate calls, not accounted against a shared budget. In particular,
   Boolean-fragment recognition now threads one shared node budget across the
   body and both endpoints (using the checking-depth value as its limit). Path
   syntax and interval arguments still receive separate
   pre-substitution node checks using that same limit. Substitution can expand
   syntax, and reduction still has no shared node or allocation budget. Fuel is not a real-time
   bound and does not protect against every oversized input.
4. Scope indices rule out out-of-scope dimension references in constructed Idris
   values; there is no raw-input decoder here, nor testing of a source parser or
   end-to-end core integration. Runtime checking and erasure of paths are absent.

Before promoting anything into the core checker, specify a bounded input-size
policy and the exact independently checked judgment and conversion interface.
For the first implementation, preserve closed computational contexts, reject
unsupported term forms before evaluation, compute both boundaries explicitly
by dimension substitution, and distinguish mismatch from exhaustion. Review
whether the duplicate toy `PathSyntax` and Boolean-only `ClosedPath` helpers
should be removed once their substitution and budget tests have equivalents.
Do not broaden the runtime or proof fragment merely because the experiment
accepts a term.

## Proposed first independent judgment

This section is an implementation contract, **not** a claim that the ordinary
core checker implements it. It deliberately specializes CCHM Figure 2 to a
closed, constant-base Boolean fragment. Write `I; · ⊢ t : A` for a dimension
scope `I` and an empty computational context. The only base type is the
existing core `Bool`; its admitted closed terms are Boolean literals and
`BoolCase` trees over admitted terms. Every embedded core term must independently
pass `checkErased` against `Bool` in `Empty`. No globals, variables, recursion,
effects, universes as endpoints, or other core forms are admitted. `I` contains
only dimensions: its entries do not add computational resources.

The intended checked path type is `Path Bool a0 a1`, where both `a0` and `a1`
are admitted checked closed core terms. For an abstraction `<i> t`, with `i`
fresh, the checker must:

1. Check `t : Bool` in `I, i; ·`, using only an explicitly specified path-body
   grammar. Check every subterm, including branches not selected by reduction.
2. Capture-avoidably substitute `i := 0` and `i := 1` in `t`, obtaining `t0`
   and `t1`. Recheck or otherwise justify the type of both resulting faces.
3. Compare `t0` with `a0` and `t1` with `a1` using bounded conversion valid for
   this fragment. A mismatch rejects; an exhausted or unsupported comparison is
   inconclusive and cannot yield a checked path.
4. For an admitted application `p r`, check `p` and the scoped interval `r`;
   beta reduction of `<i> t` is `t[i := r]`. Applications at endpoints must also
   agree with their checked boundaries. Neutral paths and path eta are not in
   this first judgment.

Initially, body terms can be closed Boolean core terms or applications of
syntactic paths whose bodies are recursively in the same grammar; no caller may
supply unverified endpoint annotations for an inner path. The current helper
collapses these inner constant paths, so its accepted examples remain constant in
meaning even if their syntax mentions a dimension. A future extension must state
and check genuinely dimension-dependent body forms rather than inferring them
from this example.

Admission must bound the input before substitution and conversion. The current
prototype has per-call node/depth checks, not a shared total-work or output-size
budget; that limitation must remain explicit until a stronger policy is
implemented. A successful judgment belongs only to this fragment: it does not
admit path evidence to ordinary Fibril programs, prove preservation or
normalization, or determine erasure and linear-resource rules. A future core
integration must define how checked judgments are represented and consumed,
and make unsupported forms fail closed in checkers and emitters.

## Checker composition gate

The experimental path helper is not an additional authority for accepting a
Fibril program. A future integrated path judgment must specify exactly which
checker validates each premise: context formation and ordinary types, cubical
formation and boundary conversion, runtime usage and erasure, and admissibility
of definitions used during conversion. Success of any one checker cannot stand
in for another. A negative result rejects; exhaustion or an unsupported premise
is inconclusive and must also prevent acceptance. Elaborator-produced syntax or
annotations are never certificates of these premises.

The current closed Boolean helper calls the ordinary erased checker and then
performs its own restricted boundary checks. It does not invoke the runtime
usage checker or a general termination checker; its closed, explicitly
terminating input grammar avoids admitting those unresolved cases. Its output is
experimental syntax, not transferable evidence that a general cubical or
resource judgment holds. The eventual composition contract must include shared
scope and substitution invariants, the status of definitions and effects,
conversion budgets, and what evidence survives erasure.

## Evidence and acceptance

- Add explicit internal positive tests for path formation, abstraction, endpoint
  checking and endpoint reduction, with scoped variables and dimension
  substitution.
- Add negative tests for mismatched endpoints/types, invalid scopes and face
  obligations, erased/linear misuse, and exhausted checking or conversion budgets.
- Test weakening, substitution, conversion and reduction interactions; include
  preservation-oriented properties where supported. Tests are evidence, not a
  proof of consistency, normalization, preservation or correct erasure.
- Keep the independent checker as the acceptance boundary. Elaborators and editor
  services must not grant unchecked path evidence. Unsupported cubical forms
  must fail closed, including in C/JS emission and runtime erasure.
- Document the precise accepted fragment, trusted assumptions and limitations,
  link runnable examples/tests, and update the README and feature matrix only
  when the implementation actually lands.

## Subsequent gates

Path types alone are not computational univalence. The next stages must specify
and implement the chosen calculus's **composition and transport**, then Glue and
the relevant computation rules before claiming computational univalence. Higher
inductive types, general rewriting, cubical source ergonomics and optimized
backends are separate later milestones. Ordering may change if the adopted
calculus requires primitives to be introduced together.

## Delivery discipline

Application work can continue, but new core, recursion, effect and backend changes
should record their interaction with this milestone: what is permitted in types,
what is erased, how reduction behaves, and what remains unproved. An application
feature must not silently turn unsupported cubical terms into runtime values or
expand the trusted proof fragment. Conversely, the cubical milestone must not
claim real-time guarantees, a production runtime, or platform interoperability.
