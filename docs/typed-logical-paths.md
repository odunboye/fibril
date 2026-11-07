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
The separately indexed extension below adds some restricted equality but not
the dependent family needed for the general square. There is no general
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
boundary; this needs a dependent PathP rule or a different square encoding.
There is no general eta, beta, interval conversion, or derivation substitution
proof, and this experiment grants no runtime authority.
