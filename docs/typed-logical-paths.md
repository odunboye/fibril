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
but not enough conversion for the general square. There is no general
weakening/substitution preservation theorem for derivations or semantic
soundness theorem here. ScopedSyntax proves separate syntactic substitution laws.

This is a declarative proof interface, not an algorithm accepting untrusted
syntax; it does not expose a runtime conversion or a checker with exhaustion.
In particular it supplies no resource admission guarantee for elaborating
untrusted Idris proofs. A future runtime checker must bound all inputs and
substitution outputs before conversion and reject unsupported cases and
exhaustion, rather than treating this proof interface as such a checker.

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

The added examples derive neutral application and endpoint equality, including
an endpoint of `p (i ∧ j)` under `i = 0`. They do **not** derive the full nested
square: the inner path has right endpoint `p i`, so the outer path's family
varies with `i`. A homogeneous nondependent path cannot express that general
boundary; this needs additional face-restricted dependent conversion or a different square encoding.
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
check constant-family PathP introduction, elimination and an endpoint. They do
not derive the requested square `λ i. λ j. p (i ∧ j)`: its boundaries need
face-restricted congruence/conversion between types such as `Path A a (p i)`
and their endpoint substitutions, and the original equality judgment could not
supply that conversion; the bounded extension below supplies only a subset. Nor is there a general derivation substitution or
weakening theorem. These rules are declarative and restricted, not equality
reflection, a semantic soundness proof, or a production runtime checker.

Additional endpoint tests use hypothetical path-over derivations with a varying
family; they do not assert that those derivations are constructible in this
slice. Their endpoint typing evidence is constructed explicitly. At an open
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
bottom at top, a term as a type, and an escaping dimension. This is a bounded
subset, not a proof of the requested square. The restricted congruences below now supply the inner edge, but not the
restricted type and equality transport needed for the outer boundaries. No general
weakening of derivations, semantic soundness theorem, or actual nested square
is claimed.


## Typed interval and dependent abstraction congruence

`IntervalEquivalent` is deliberately a very small sufficient relation, not a
Boolean-vertex solver: reflexivity and `i ∧ j = i` when the bounded syntactic
face entailment checks `j = 1`. The latter uses the existing 12-dimension,
12-face-node bounded check; the interval expression is not traversed by a new
solver. This is an elementary lattice identity under the checked assumption,
not an Idris semantic soundness theorem. `NIntervalApplyCong` requires one
and the same typed path with a nondependent carrier on both sides. It does not
identify different paths or invent equality of dependent result types.
`NPathPAbstractCong` requires two complete abstractions of the identical family
and endpoints, and body equality at that family on the weakened face.

`squareInner` derives `λ j. p (i ∧ j) : Path A a (p i)` in the explicit
neutral path context. Its left boundary uses the typed path endpoint rule and
its right boundary the new interval congruence. The full nested square is not
claimed: under the outer endpoint face its inner abstraction must be compared
with the chosen outer endpoint at the varying family, whose endpoint types
only agree by restricted `NPathTypeCong` and `NConvert`. The existing equality
judgment has no conversion/transport rule to move a derived equality to that
converted type, nor general face weakening to establish all abstraction typing
premises at the exact nested faces. These missing typed derivations are not
assumptions. There is no general eta/beta, semantic soundness theorem, or
production checker change. Negative fixtures check non-Boolean collapse,
distinct path identities, invalid face evidence, dimension scope, and unrelated
dependent-abstraction endpoints.
