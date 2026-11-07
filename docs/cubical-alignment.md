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

## General-path continuation

The [quantitative cubical rule sheet](quantitative-cubical-rules.md) now specifies
proposed checking authorities, the runtime conversion firewall, open logical
path examples, and ordered proof/implementation gates. It supersedes the
closed-only next-step scope below. It is a proposed contract, not implemented
support or a completed soundness argument. The existing closed-Boolean API
remains a regression baseline; general logical paths are the next target.

## Original next vertical slice (historical roadmap)

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
checked-path witness, embed an open computational variable, or reference an
out-of-scope dimension. It does not run the CLI or native test suites. Avoid concurrent builds
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
   `formClosedBoolPath` separately checks and seals the two endpoint terms;
   `checkPathAgainstType` checks an abstraction against that formed type, and
   `checkPathEndpoint` rechecks and seals an endpoint result. The optional
   `checkRuntimePathEndpoint` additionally checks that *ordinary closed Boolean
   result* with `checkRuntime` in `Empty`, producing a distinct opaque runtime
   endpoint witness. Forgetting that witness exposes only the ordinary core term.
   This does not validate the path as a runtime value or establish any
   quantitative cubical rule.
   Distinct endpoints may form a type without yielding a path.
   `checkCorePathExpr` itself returns only a status; callers must not treat raw
   `CoreStepped` syntax as a reusable typing certificate. Witness construction
   distinguishes rejection from exhaustion with `ClosedPathFailure`, whose
   constructors cannot express success. Applying a witness rechecks its recorded
   inputs under the supplied budgets. `applyCheckedPathAt` first weakens a
   checked closed path into an open dimension scope and returns raw substituted
   syntax; that result is not itself a checked witness. The path/interval-node
   admission limit is checked before weakening, but it does not count embedded
   core payloads or bound total allocation.
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
   syntax and interval arguments still receive separate pre-substitution node
   checks using that same limit. Open checked application also preflights its
   substituted path/interval output, charging repeated replacements in full.
   This is not a bound on core payloads, all intermediate weakening, or total
   allocation; reduction still has no shared node or allocation budget. Fuel is not a real-time
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

## Internal checked-path demonstrator

The test `checked path milestone forms checks and checks both endpoint results`
in `test/src/Tests/Main.idr` now performs the narrow internal sequence: form
`Path Bool False False`, check a constant abstraction whose body reduces to
`False`, apply it at both endpoints, independently recheck each result against
its boundary, and compare both results to `False`. `IndependentPath.idr`
provides opaque experimental witnesses for the formed type, checked path and
checked endpoint results. Negative tests cover forged witnesses, scope, mismatched
boundaries, unsupported core syntax and exhausted budgets.

This demonstrates the endpoint objective only for the isolated closed Boolean
fragment. It is not a path constructor in `Fibril.Core.Term`, is not connected
to the ordinary core acceptance boundary or backends, and does not settle the
remaining quantitative, general conversion, or soundness obligations. In
particular it is not HoTT support. The broader milestone's independent core
integration and resource tests remain open.

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

## Quantitative integration: research blocker

CCHM Figure 2 does not specify Fibril's `0/1/ω` usage judgment. One relevant
reference is Abel, Danielsson and Vezzosi, [*Compiling Programs with Erased
Univalence*](https://www.cse.chalmers.se/~nad/publications/abel-danielsson-vezzosi-erased-univalence.pdf),
§4.1.4 and Figure 4. Their CTT0 gives path and cubical rules with erasure, and
§3 demonstrates why seemingly harmless combinations of erasure and equality
can produce observably incorrect compiled results. **CTT0 explicitly supports
only erasure, not linearity** (§7); it cannot be adopted as a justification for
Fibril's `1` quantity. Its compilation result also relies on stated assumptions
(§4.3). It is a candidate reference for investigating an erased fragment, not
an adopted Fibril calculus or a proof about this implementation.

A concrete unresolved obligation is resource preservation for dependent
transport: a reduction for a dependent pair may place the transported first
component both in the first projection and inside the type family used for the
second. Whether those occurrences are erased or consume a linear value depends
on the exact typing and erasure rules. More broadly, converting a type along an
ordinary univalent equivalence must not silently turn an unrestricted function
into a resource-preserving linear one. These problems are not resolved by
counting occurrences in the initial syntax or by passing existing runtime tests.
The [Cubical Agda linearity discussion](https://github.com/agda/agda/issues/4642)
records these examples and explicitly labels its proposed restrictions as
unverified; it is motivation, not an adopted specification.

### A concrete obstruction to naive quantitative endpoint rules

Consider a hypothetical runtime path value `p : Path A a b` whose endpoints are
used only in erased type annotations. Suppose a proposed application rule
charges one runtime use of `p`, and also adopts CCHM's typed endpoint conversion
`p 0 ≡ a : A` for a neutral `p`. In a linear context, `p 0` appears to consume
`p` once, whereas `a` need not consume `p` at all; if `a` mentions an erased
variable it may not even be a legal runtime expression. Thus that conversion is
not by itself a usage-preserving runtime rewrite. This is a counterexample to
that **combination of proposed rules**, not a claim that CCHM or any particular
quantitative calculus is unsound. Treating the equality only as erased
conversion does not automatically solve the problem: type conversion and any
optimization using it must still be shown not to change observable resource
use.

A candidate design must decide separately whether paths themselves can be
runtime values, whether application at endpoints is allowed in runtime
judgments, what quantities endpoints have, and whether endpoint equations are
runtime reductions, erased conversion, or both. For every chosen equation it
must prove typing and usage preservation (or a precisely stated simulation that
preserves resource observations), including neutral paths and endpoints that
mention erased or linear variables. Merely charging the path operand once is
insufficient. Restricting observations to erased judgments is one candidate to
investigate, not a proven solution: dependent transport and interaction with
ordinary conversion would still require a theorem.

Two further references help separate possible approaches, without closing this
gap:

- Atkey, [*Syntax and Semantics of Quantitative Type Theory*](https://doi.org/10.1145/3209108.3209189),
  §2.2–2.3, proves substitution for its QTT and gives a counterexample for an
  earlier system with arbitrary result usages. Its `0/1/ω` resource algebra is
  relevant, but its calculus does not provide CCHM path or composition rules.
  A Fibril integration would need to establish that its existing judgments and
  proposed cubical extension satisfy the corresponding substitution premises;
  citing QTT alone does not establish that.
- Doré, [*Linear Types inside Dependent Type Theory*](https://msp.cis.strath.ac.uk/types2025/abstracts/TYPES2025_paper91.pdf)
  (TYPES 2025), §1–2, describes a deep embedding of linear entailment in
  Cubical Agda and proposes additional structure for dependent linear function
  types. This is a different architecture from Fibril's built-in usage checker:
  its Cubical Agda embedding is not a preservation or erasure theorem for
  Fibril's runtime and cannot be transplanted as a path-typing rule.

Until a published compatible calculus or a justified conservative design is
selected and its preservation/substitution/erasure obligations are addressed,
the independent closed fragment must not be promoted to a core path constructor
accepted in linear contexts. In particular, a proof-only annotation or a blanket
rule that all path data erase is not enough. The existing empty computational
context and restricted Boolean grammar avoid captures for the experiment only;
they are not rules for weakening into arbitrary linear contexts or for transport.

## Candidate closed-Boolean core boundary (experimental API, not integrated)

A conservative first integration can compile an endpoint observation to an
**ordinary** `Term 0`, rather than introducing a runtime path representation.
The proposed entry point accepts a closed raw path and closed Boolean endpoints,
checks formation and both boundaries using the restricted judgment above, and
accepts only a literal endpoint `0` or `1`. It then independently checks the
result as `Bool` with the ordinary runtime checker in `Empty`. Any unsupported
form, mismatch, or exhausted component check must prevent emission. The output
is the checked ordinary Boolean expression, not a path or a proof that can be
used as a core type. Its erasure and execution are therefore exactly those of
that existing core expression. `lowerClosedBoolEndpoint` implements this sequence
as an experimental API returning an opaque runtime-checked Boolean witness; it
is not wired into elaboration or code generation. This describes a compile-time
lowering boundary, not general path support or a new `Fibril.Core.Term` constructor.

The integration is acceptable only if all of these obligations are met:

1. The boundary is invoked before ordinary checking and code generation; raw
   path syntax or annotations must not bypass it. The emitted term is rechecked
   by the ordinary pipeline rather than treating an experimental witness as a
   transferable typing derivation.
2. The input's embedded ordinary terms have computational scope zero by
   construction, and the accepted Boolean grammar excludes variables,
   definitions, effects and recursion. Dimension scope and substitution remain
   separate from computational scope. An enclosing program may consume the
   resulting closed Boolean as an ordinary expression, but this does not allow
   the original path to capture its variables.
3. Both boundaries are independently checked, even when only one is observed;
   the selected result is checked against its declared endpoint. Tests must
   cover the opposite boundary being wrong, non-Boolean payloads, open captures,
   unsupported observations and exhaustion at every stage.
4. The metatheoretic target is a conservative elaboration argument: every
   accepted observation elaborates to the exact closed core term independently
   checked and emitted, and no path-specific reduction or typing rule is added
   to the core. This argument depends on correctness of the restricted path
   checker and the existing core pipeline; finite tests are not a proof.
5. Current budgets remain independent per call and do not bound total work or
   allocation. A production-facing boundary requires a separately specified
   resource policy and tests for it before admitting untrusted input.

If first-class paths in `Fibril.Core.Term` are required instead, this lowering is
insufficient: constructor handling must be specified and audited across renaming,
substitution, equality, both checkers, reduction, evaluation, serialization and
all backends. In particular, a closed payload embedded in an open term must not
be mistaken for a proof that arbitrary paths are closed or erased. No such
constructor is authorized by this candidate alone.

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

## Experimental reusable telescope paths

`Fibril.Cubical.Logical.ReusablePath` checks an abstraction against open
first-order telescope endpoints on both faces and returns an opaque witness
indexed by the exact telescope, body and endpoints. Application substitutes a
scoped interval for the newest dimension, preserving older dimensions, and
bounds its inputs and output. The witness does not carry an arbitrary caller
supplied conversion environment; endpoint comparisons use the ordinary
face-restricted telescope conversion. Admission and conversion are bounded and
incomplete: rejection or exhaustion is not a proof of inconsistency.

This is an isolated one-dimensional API over `Tvar`/`Tapp`, not a new trusted
core feature, quantitative path judgment, or general higher-path calculus.
A body may depend on another dimension, but path-valued endpoints are not
represented. `Square.applySquare` fixes either i or j, retaining the other as
the path binder and instantiating its two edges. Its result is independently
checked by `checkPath`; a checked square alone does not establish the resulting
abstract endpoint equalities in this incomplete fragment. `Rejected` means the
checker could not prove them, not that they are unequal; `Exhausted` indicates
an admission bound. Input and transformed output each have separate 32-node
hard caps and use the supplied allowance; the independent path checker imposes
its own 12-node cap and allowance. These are admission bounds, not operation
fuel. Scoped substitution lifts the replacement under the retained binder.
The total pure index maps `fixSquareI`, `fixSquareJ`, and
`instantiateSquareEdge` are public so clients can reduce the exact result
indices. Calling them directly performs no admission or checking and grants no
witness; bounded witness construction remains exclusively in `applySquare`.
No runtime conversion or general nested path claim follows. See
`Tests.Cubical.OpenPath`, `Tests.Cubical.ReusablePath`, and the opacity fixtures.

The proof-producing `TypedPathChecker` also admits the inner connection edge
`<j> p@(i ∧ j) : Path A (left p) (p@i)` for an existing dimension `i`.
It constructs endpoint and interval-congruence derivations on the two restricted
faces. `checkNeutralEqual` separately checks `p@(i ∧ r) = p@i` when its
bounded face entailment proves `r = 1`, and `p@r = left/right p` when it
proves the relevant endpoint. The latter equality grammar is directional and
requires a variable as the retained meet factor. These are sufficient rules,
not a complete equality decision procedure; in particular they do not identify
`i ∧ ~i` with zero. The checker does not yet construct the full dependent
square, perform general recursive PathP checking, or synthesize varying-family
type conversion. Admission shares a 128-node maximum across inputs and caps
context and dimension sizes at 12; bounded entailment may still reject an
admitted case as unsupported.
