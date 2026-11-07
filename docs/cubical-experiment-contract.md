# Frozen experimental calculus: Common Path v0

Status: **consolidation baseline, not production admission or full cubical type theory**.
Frozen from repository revision `247e517`. This document selects the authoritative
experimental contract; historical milestone documents do not enlarge it.

## Decision and boundaries

Use `Fibril.Cubical.Logical.ShadowCommon` as the authoritative declarative
ordinary-term, named-path, face-equality and homogeneous abstraction judgment.
Use its **environment-dependent higher-order setoid interpretation** as the
selected semantic validation model. Its additional witness, alignment and
admissibility premises are part of the theorem contracts, not silently discharged.

This choice preserves Boolean, unit and function types, typed ordinary contexts,
arbitrary typed ordinary declaration endpoints, and the existing source-shadow
translation. It does not discard the distinct dependent-path research in
`TypedPath`: restricted PathP is a separate reference experiment, not a rule of v0.

No module is deleted or renamed in this freeze. Existing public Idris constructors
remain accessible; “frozen” is a project scope decision, not an enforced module
visibility boundary. No new parser, production conversion or runtime authority is
introduced.

## Supported language and rules

Ordinary types are `LogicalType`: Unit, Bool and nondependent arrows. Ordinary
contexts and named-path type contexts are separately indexed vectors. Dimension
contexts are finite scopes. Quantities are **not** part of common typing: they
remain in the source quantitative judgment.

| Rule family | Authoritative implementation | Established contract | Remaining obligation |
| --- | --- | --- | --- |
| Ordinary formation/typing | `CommonTerm`, `CommonHasType` | Scoped variables, Unit/Bool, lambda/application, conditional, unit elimination | `CommonAdmission` admits scoped annotated raw typing; production correspondence remains open |
| Ordinary substitution | `CommonSubstitutionTyped`, `substituteCommonTyped` | Typed environments preserve ordinary typing; translation commutation | Production checker correspondence |
| Dimension-scoped bodies | `CommonPathTerm`, `CommonPathHasType` | Ordinary embeddings, named application, lambda/application, if/unit | `CommonAdmission` admits scoped annotated bodies and canonical-context endpoint equality; abstraction admission remains open |
| Named declarations | `CommonDeclarations`, `CommonDeclaredPath` | Dimension-independent typed ordinary endpoints, exact typed name lookup | `CommonAdmission` retains checked endpoint witnesses; canonical semantic validity is an explicit model premise, automatically converted to existing admissibility |
| Face equality | `CommonFaceEqual` | Typed reflexivity, declared endpoints, symmetry/transitivity, stronger-face restriction, app/if/unit congruence | `CommonAdmission` constructs canonical-context endpoint/restriction and compositional evidence in a separate API; no lambda equality or beta/eta rule is added |
| Homogeneous abstraction | `CommonShadowPath` / `CommonAbstract` | Typed body under fresh dimension and both actual face-restricted boundaries | Automatic construction of complete semantic certificates |
| Application | `applyCommonShadowPath` | Capture-avoiding substitution for fresh dimension | Production elaboration/reduction correspondence |
| Term substitution of judgments | `substituteCommonDeclarations`, `substituteCommonFaceEqual`, `substituteCommonShadowPath` | Independent typed substitution preserves declarations/equalities/abstractions | Integrated quantitative cubical preservation |
| Dimension substitution | `CommonDimensionEvidence`, `CommonPathDimensionEvidence`, `mapCommonShadowPathDimensions` | Rebuilds actual judgments with renewed indexed checks | Automatic recertification; unconditional stability is not claimed |
| Interpretation | `HigherOrderTerm`, `HigherOrderPathTerm`, `dependentPathSemantics` | Explicit computational witnesses interpret as extensional setoid morphisms | `CommonAdmission` constructs typing witnesses automatically; complete equality/boundary certificates remain open |
| Semantic equality | `DependentEndpointFaceEvidence`, `dependentEndpointFaceEvidenceSound` | Actual derivations sound with explicit structural evidence and admissibility | Every admitted equality must construct this evidence |
| Semantic abstraction/application | `HigherOrderCommonShadowPath`, `higherOrderCommonPathBoundary`, `higherOrderCommonPathApplicationRelated` | Exact witnessed abstraction/application and both endpoint relations | Automatic boundary evidence; full cubical model |

Boundary faces weaken the ambient restriction and conjoin the fresh endpoint.
Restriction checks **new face entails old face**. Endpoint equality's result type
must be the declared path's type; preserve the regression for the corrected
`CommonLeft` and `CommonRight` signatures.

## Quantity and executable authority

`Core.Quantitative` supplies the separate pure source syntax and `Uses` judgment.
`shadowTerm` and common translation are one-way. Source substitution results
require actual `Uses` and `ReplacementUses`; common equality cannot recover them.
The paired substitution theorems do not assert arbitrary path endpoints equal
the accompanying source term.

The v0 logical grammar has no globals, general recursion, effects, acquisition,
or handles. Production Fibril supports features outside that grammar. They are
not admitted through this experiment, even if erased. A future production bridge
must specify a total logical-definition boundary before importing globals or
recursive computations into conversion.

Logical equality grants no cast, quantity change, layout change, handle creation,
region change, generation refresh or cleanup authority. Runtime interfaces and
ownership checks remain separately authoritative for execution.

## Checking, exhaustion and cost

The selected calculus itself is a declarative Idris proof interface.
`CommonAdmission` now supplies a bounded, evidence-producing first typing slice
for scoped annotated raw ordinary/path syntax and first-order face-equality
certificates (including declared endpoints under canonical semantic validity);
see [its exact contract](common-admission.md). `TypedPathChecker` is not its
checker. The full abstraction admission contract, including automatic
construction of both boundary semantic certificates, remains open.

Existing bounded entailment checks are incomplete. Unsupported cases and
exhaustion must reject certificate construction; `False` is not a proof of
non-entailment. Dimension mapping requires fresh checks, not assumed stability.
Proof-node fuel, syntax preflight and solver caps are different measures. Neither
arbitrary host substitutions nor existing declarative proofs provide a total
untrusted time/allocation guarantee.

## Module disposition

| Modules | Role after freeze |
| --- | --- |
| `ShadowCommon` | Authoritative v0 judgments and selected dependent semantic model |
| `CommonAdmission` | Isolated annotated typing, raw declarations, preserved reflexive API and separate canonical-context endpoint/restriction equality admission with exact computational/semantic evidence; no abstraction admission |
| `Shadow`, `ShadowSubstitution` | Intrinsic pure source-shadow language and proved source translation dependencies |
| `ShadowPath` | Source-side path representation and translation/recertification dependency; not a competing production language |
| `ShadowTypedBridge` | Restricted compatibility bridge; not the type-preserving v0 target |
| `TypedPath`, `TypedPathChecker`, `ScopedSyntax` | Reference experiment for abstract-base/restricted PathP checking and scoped syntax; no automatic rule import into v0 |
| `OpenPath`, `FaceSoundness` | Shared interval/face machinery and model-specific soundness dependencies |
| `PathContext`, `Telescope`, `Square`, `ReusablePath` | Retained scoped-context/square regression and reference experiments |
| `Cubical.RuntimeInterface` | Separate executable-interface experiment; no equality-to-runtime bridge |
| `Foundation.DeMorgan` | Shared interval infrastructure; production normalization proof gaps remain separate |

Independent-path and first-order semantic slices inside `ShadowCommon` remain
reference/regression models. Do not combine their assumptions with the selected
environment-dependent model without an explicit theorem.

## Explicit exclusions

No general dependent types or PathP, universes, systems, composition/filling,
logical dependent transport, Glue, univalence or HITs are selected into v0.
The finite four-pair model is not a free De Morgan completeness theorem or a CCHM
presheaf model. Finite valuation substitution results do not establish general
cubical naturality or fibrancy. No full production normalization, erasure,
execution or ownership soundness theorem follows from v0.

## Next gate: complete evidence-producing admission contract

The [first admission slice](common-admission.md) constructs exact ordinary/path
typing and computational witnesses, without caller-supplied conclusions. It does
not complete the abstraction gate or provide general conversion. Raw declarations,
reflexive certificates and canonical-context declared endpoint/restriction
certificates are now checked automatically, with no new v0 equations. Before adding
language rules, finish the remaining obligations of a raw-input interface that:

1. Admits exact ordinary, named-path, dimension and face contexts.
2. Produces `CommonPathHasType` and exact equality/abstraction derivations.
3. Produces required computational witnesses and structural alignments.
4. States semantic context admissibility as an explicit assumption, not an
   arbitrary Boolean certificate or a promised existence theorem.
5. Constructs semantic equality/boundary evidence for each supported rule.
6. Rejects unsupported/exhausted checks with no runtime conversion fallback.
7. Specifies separate input, expansion, solver and proof-search budgets.

The first end-to-end acceptance example must contain an open nonconstant path,
a genuinely linearly used source term, both endpoints and dimension substitution.
Keep diagnostic-specific wrong-type, wrong-face, wrong-index, erasure-reflection
and exhaustion regressions. Run `bash tools/test_cubical_worktree.sh`, then broader
hosted/native/ownership regressions at an integration gate.

## Freeze change policy

Bug fixes, proof completion, evidence-producing admission and module refactoring
that preserve these rules are in scope. New equality rules, dependent families,
composition, production imports or runtime authority require a separate design
change stating preservation, semantics, cost and regression obligations. Do not
call passing tests a general theorem, or manual semantic evidence automatic
checker soundness.
