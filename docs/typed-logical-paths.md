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
`p (i ∧ j)` with neutral path `p` is not: path assumptions, typed restricted
conversion and equality of boundary path types are missing. There is no general
weakening/substitution preservation theorem for derivations or semantic
soundness theorem here. ScopedSyntax proves separate syntactic substitution laws.

This is a declarative proof interface, not an algorithm accepting untrusted
syntax; it does not expose a runtime conversion or a checker with exhaustion.
In particular it supplies no resource admission guarantee for elaborating
untrusted Idris proofs. A future runtime checker must bound all inputs and
substitution outputs before conversion and reject unsupported cases and
exhaustion, rather than treating this proof interface as such a checker.
