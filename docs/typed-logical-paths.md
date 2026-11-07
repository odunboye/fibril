# Declarative nondependent path slice

`Fibril.Cubical.Logical.TypedPath` is isolated from the production checker. It
interprets `ScopedSyntax.Universe` as an abstract base A, not a universe. Its
implicit context consists of `m` variables all of type A, and `n` scoped
interval dimensions. There are no user-supplied context type annotations.

The judgments `TypeFormed a` and `HasType t a` are Idris datatypes whose indices
are the exact scoped syntax. They give formation of A and nondependent paths,
base-variable introduction, path abstraction, and application at a scoped
interval. Path formation requires a formed carrier and endpoints typed at that
carrier. Abstraction requires the same plus a body typed at the weakened
carrier and *both* propositional equalities between its capture-avoiding face
substitutions and the claimed endpoints. Application requires a path derivation;
an arbitrary `Path` annotation cannot supply one. Constructors are deliberately
public proof rules, not opaque runtime checker results. Idris checks the evidence.

This is a strict syntactic subset of the ordinary rules of [CCHM §3.1,
Figure 2](https://arxiv.org/html/1611.02108#S3.SS1), not dependent PathP,
univalence, or an implementation of their full conversion. In particular the
boundary evidence is equality of syntax, not face-restricted conversion; no
beta, endpoint, De Morgan, or eta conversion is assumed. Nested constant
paths and a dimension-varying application are derivable, but a general square
`p (i ∧ j)` with neutral path `p` is not derivable in this original judgment.
The separately indexed extension below adds restricted dependent families and equality,
and derives this square under a declared neutral path context. There is no general
weakening/substitution preservation theorem for derivations or semantic
soundness theorem here. ScopedSyntax proves separate syntactic substitution laws.

The original judgments are a declarative proof interface, not themselves an algorithm accepting untrusted
syntax; it does not expose a runtime conversion or a checker with exhaustion.
In particular it supplies no resource admission guarantee for elaborating
untrusted Idris proofs. The experimental bounded checker described below accepts a much smaller grammar and is not a production runtime checker.

## Neutral declarations and restricted judgments

A separate experimental syntax `NeutralExpr` uses separate indices for base
variables and neutral paths. `PathContext` declares each path with two base
variable endpoints, so a path declaration cannot refer to itself or another
path. `NeutralTypeFormed`, `NeutralHasType` and `NeutralEqual` are indexed by
the exact context, face, type and terms. Their rules include nondependent path
formation and abstraction, application, restricted endpoints and pointwise
abstraction congruence. Endpoint rules require exact typing and a checked
Boolean face entailment equation. The deliberately incomplete syntactic
entailment admits at most 12 dimensions and 12 combined face nodes; it does not
use Boolean vertex logic. It is not accompanied by a semantic soundness proof.
No opaque converter evidence is embedded in the judgment.

The examples derive neutral application and endpoint equality, including an
endpoint of `p (i ∧ j)` under `i = 0`. The full nested square below uses a
varying outer PathP family; a homogeneous nondependent path cannot express it.
There is no general eta, beta, interval conversion, or derivation substitution
proof, and this experiment grants no runtime authority.

## Restricted dependent path-over rules

The neutral judgment also has `NPathPForm`, `NPathPIntro`, and `NPathPElim`.
The family is formed under the weakened face in one extra dimension; endpoint
checking uses the actual zero and one substitutions into that family. The body
is checked at the varying family, and its boundary equalities are checked at
that family under the respective restricted faces. Elimination substitutes the
argument interval for the family binder. Endpoint rules require the endpoint
itself to be typed at the instantiated carrier under the current face, in
addition to the bounded entailment proof. This extra premise deliberately avoids
assuming dependent type conversion under a face. Existing nondependent rules
remain unchanged.

The tests form a genuinely varying family whose endpoints are both `p i`, and
check constant-family PathP introduction, elimination and an endpoint. The square derivation below also uses restricted path-type congruence and
face restriction for its boundaries. There is no general derivation substitution
or weakening theorem. These rules are declarative and restricted, not equality
reflection, a semantic soundness proof, or a production runtime checker.

Additional endpoint tests use hypothetical path-over derivations with a varying
family; those particular tests are conditional, independently of the concrete
square derived below. Their endpoint typing evidence is constructed explicitly. At an open
argument constrained to zero, typing the endpoint only at the zero-substituted
family is rejected, while an endpoint typed at the open instantiated family is
accepted. Substitution under a nested abstraction is checked definitionally to
preserve the inner binder. Separate negative examples reject a body of the wrong
type and a reflexive proof of the wrong varying-family boundary.

## Bounded type congruence and conversion

`NeutralTypeEqual` adds reflexivity for a formed type and congruence for
**nondependent** path types over the same formed carrier. Both pairs of
endpoints must be typed at that carrier and related by `NeutralEqual` at the
same context and face. Thus both path types are formed by `NPathForm`; no
endpoint equality alone identifies arbitrary types. `NConvert` changes a term's
type only with this type-equality evidence at the identical context and face.
This is the restricted path-congruence and conversion instance of CCHM's
judgmental equality rules, not equality reflection. It does not include
congruence of genuinely varying PathP families. Its path-family binder is
exactly the existing `weakenNeutralDimensions a`; it introduces no unlifted
face under a binder. Existing PathP rules continue to use `weakenFace`.

The new concrete example converts the constant path at `p i` from
`Path A (p i) (p i)` to `Path A a a` on `i = 0`, using the typed endpoint
rule twice. Negative fixtures reject unrelated endpoints, reusing evidence from
bottom at top, a term as a type, and an escaping dimension. `NEqualConvert` transports a term equality only using explicit type equality
and typings of both terms at the destination, at the very same context and
face. `NSym` reverses a typed equality. `NFaceRestrict` permits typing on a
stronger face only when bounded entailment proves that it entails the source
face; it cannot carry bottom evidence to top. These are explicit declarative
rules, not equality reflection or a general weakening theorem.


## Typed interval and dependent abstraction congruence

`IntervalEquivalent` is deliberately a very small sufficient relation, not a
Boolean-vertex solver: reflexivity and `i ∧ j = i` when the bounded syntactic
face entailment checks `j = 1`, plus the symmetric left-one rule. The latter uses the existing 12-dimension,
12-face-node bounded check; the interval expression is not traversed by a new
solver. This is an elementary lattice identity under the checked assumption,
not an Idris semantic soundness theorem. `NIntervalApplyCong` requires one
and the same typed path with a nondependent carrier on both sides. It does not
identify different paths or invent equality of dependent result types.
`NPathPAbstractCong` requires two complete abstractions of the identical family
and endpoints, and body equality at that family on the weakened face.

`squareInner` derives `λ j. p (i ∧ j) : Path A a (p i)` in the explicit
neutral path context. Its left boundary uses the typed path endpoint rule and its right boundary
interval congruence. `square` is a closed Idris derivation, with no hypothetical
judgment premises, under the declared neutral context `a : A, b : A, p : Path A a b`:

```text
λ i. λ j. p (i ∧ j)
  : PathP (λ i. Path A a (p i)) (λ j. a) (λ j. p j)
```

Both outer endpoint abstractions are independently typed at their instantiated
families using path-type congruence, and both boundary equalities are derived at
the exact restricted faces. The right boundary uses the left-one interval rule;
the left uses the endpoint rule. This is a declarative derivation, not a
production checker feature or semantic soundness theorem. There is no general
eta/beta or dependent-family type congruence. Negative fixtures cover unrelated
carriers, bottom-face escape, failed endpoints, face indices and distinct neutral
paths, among other scope and premise failures.


## Bounded neutral checker

`Fibril.Cubical.Logical.TypedPathChecker` is an isolated, deliberately incomplete
algorithm. `checkNeutral` returns either an error or the actual public
`NeutralHasType ctx face term ty` derivation at exactly the supplied indices;
`checkNeutralFormation` similarly returns `NeutralTypeFormed`. These are not
opaque certificates: the declarative constructors remain public and Idris
checks their premises. In particular endpoint derivations use propositional
proofs of the actual `boundedFaceEntails` equations, not a Boolean assertion.

Accepted terms are base variables at `NType`, declared neutral paths at their
exact declared base-variable endpoints, applications of declared neutral paths
at any scoped interval at `NType`, constant base-variable abstractions at
`Path A x x`, and abstractions `\i => p i` at precisely p's declared
endpoints. It also accepts the connection inner edge `\j => p (i ∧ j)` at
`Path A (left p) (p i)` when `i` is an existing dimension variable. Its
boundaries are derived under the appropriate restricted faces by endpoint and
interval congruence rules. Formation accepts `NType` and `Path A l r` when both
endpoints are accepted terms at `NType`.

`checkNeutralEqual` produces typed base reflexivity, endpoint equalities in
either orientation, and congruence of applications of the same declared path
at structurally identical intervals or either meet-one identity (also in
either orientation). Retained meet factors may be arbitrary scoped intervals.
Both endpoint rules are tried when the declared endpoints coincide. Different
declared paths are not identified merely because they have the same endpoints.
The structural interval comparison recursively returns equality evidence; it
does not use Boolean vertices or identify `i ∧ ~i` with zero.

`checkNeutralTypeEqual` checks `NType` reflexivity and face-sensitive
congruence of `Path A` types using four checked endpoint typings and two
proof-producing base equalities. `checkNeutralPathEqual` checks both abstractions at the exact requested base
path type and compares their bodies at the weakened face. It is restricted to
the abstraction forms already accepted by the typing checker. Neither checker
yet synthesizes conversion into the typing checker. The full nested PathP square is
therefore still declarative only: its outer boundaries require checking both
abstractions at a common restricted path type using endpoint type conversion,
then proving their bodies equal at the weakened restricted face. General PathP
also requires preflight of dimension-substitution outputs before allocating them.

All syntax, including both annotations and the face, shares an admission
allowance capped at 128 nodes; base, path, and dimension counts are capped at
12. Scoped `Fin` indices and `PathContext` enforce scope and endpoint
formation. Admission happens before comparisons, entailment, or face weakening;
the latter creates at most the admitted face plus two nodes. No term
substitution is performed, hence no substitution output is allocated. The
fixed grammar does bounded structural comparisons and capped entailment calls;
equality endpoint and meet goals have size linear in the admitted interval.
`Exhausted` reports admission failure, `Mismatch` reports a definite mismatch
within the implemented shapes, and `Unsupported` reports other shapes or an
endpoint entailment the bounded procedure cannot prove (including its 12
dimension/12 face-node limits). False faces do not enable extra conversions.
The checker has no production elaboration or runtime authority.
