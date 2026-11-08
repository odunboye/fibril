# Initial term core and quantity rules

Status: proposed typing rules with implemented scoped syntax and structural operations.
Not a completed calculus or soundness proof.

## Finite variants and the next extension

The [inductive-data landing plan](inductive-data.md) specifies a finite-variant
kernel before named data, recursive inductives and structural recursion.
[Finite variants](finite-variants.md) are now implemented in the internal kernel;
[closed nominal identity](nominal-data.md) and [source data](data.md) expose
checked constructors, direct non-recursive cases and named elimination. A
fixed terminal/unary-self and parameterized list-shaped types with structural
folds are implemented. General recursive data and [indexed families](indexed-data.md)
are checked in a restricted whole-field positive fragment; nested and mutual
recursive declarations remain future work. Nullary arms have
an explicit representation; hidden Unit padding does not support the required
dependent motives under current Unit conversion.

## Theoretical correspondence

See [ATKEY18](references.md#atkey18), especially §§2.1–2.3, for semiring usage,
erased/present judgments, and the substitution pitfall. See
[DEBRUIJN72](references.md#debruijn72) for nameless binding background.
Our scoped representation and local allows policy do not implement the paper's
full judgments. These references justify design questions, not Fibril soundness.

## Staging and trust

Implement a deliberately small ordinary dependent-function fragment before
connecting it to cubical terms. This fragment is a stepping stone, not a claim
that CCHM plus these quantities is sound.

Keep dimension contexts and term contexts separate. Existing restriction
contexts hold face assumptions only. No general recursion, partial definitions,
axioms, or unsafe primitives enter this initial logical fragment.

## Proposed initial grammar

    Level ::= natural number
    Term  ::= Var index
            | Universe Level
            | UnitType
            | UnitValue
            | UnitCase Term Term
            | BoolType | BoolTrue | BoolFalse
            | BoolCase Term Term Term
            | StringType | StringValue text
            | Pi Quantity Term Term
            | Lam Quantity Term Term
            | App Term Term

Indices are de Bruijn indices; 0 is the newest term variable. Pi and Lam bodies
extend the term scope; their domain annotations do not. Domain annotations on
lambdas simplify explicit core checking before surface inference exists.

Universe levels initially are literal natural numbers, with Type l : Type (l+1)
and Pi formation at max of domain/codomain levels. No Type : Type.
[Literal universe compatibility](cumulativity-rewriting.md) is now implemented
separately from conversion. Constructor propagation, level polymorphism, and
impredicativity are not implicitly included.

Core syntax, substitution, evaluation, conversion, and typing must each receive
tests. Representation alone is not a checker.

## Implemented primitive Unit

[Unit](unit.md) adds UnitType : Universe 0 and UnitValue : UnitType. Both are
closed atoms under renaming/substitution and have no reduction rules. Runtime
UnitValue uses no variables; UnitType, like other type expressions, cannot be
executed as a value. UnitCase explicitly consumes a Unit scrutinee before its
body, adding their usage; it introduces no binder and contracts on UnitValue.
No dependent motive, eta rule, or implicit linear discard is provided.

## Implemented Boolean branching

[Bool](boolean.md) adds a type in Universe 0, two zero-usage constructors,
and a nondependent conditional. Both branches must have equal normalized types.
Runtime branches use a pointwise [permission join](alternatives.md); the
condition's usage is added to that join, not both alternatives. Matching 1/1
observations stay linear; differing observations require unrestricted permission.
The finite permission law is proved in Idris 2, not a term preservation theorem.

## Implemented pure String

[String](strings.md) adds StringType : Universe 0 and StringValue text : StringType.
Both are scope-independent atoms; literals contribute zero runtime usage and
compare by exact literal data. There is no new reduction, eliminator, Unicode
normalization, IO behavior, or implicit quantity coercion.

## Implemented unary wrappers

[Quantity-aware unary wrappers](unary-records.md) add BoxType, BoxValue and
BoxCase for singleton records. Formation preserves the domain universe;
dependent elimination checks an erased motive and exact field quantity, then
reduces to one ordinary application. No hidden Unit padding, eta rule or
preservation/erasure theorem is introduced.

## Experimental IO descriptions

[IO rules and the Fibril prelude](console-runner.md) now type pure effect
descriptions. IOType preserves its operand's universe; Pure packages a value;
WriteLine consumes a String operand and describes IO Unit; Bind combines an
IO A action with a linear A -> IO B continuation. Runtime usage adds action and
continuation usage. Bind over Pure reduces to application; no core operation
performs host IO or extracts an IO A as trusted evidence of A.

## Proposed quantity accounting

Coefficients are 0, 1, and omega (unrestricted):

- Addition: 0 is identity; any sum of two nonzero coefficients is omega.
- Multiplication: 0 annihilates; 1 is identity; omega times omega is omega.
- A usage vector records computational use of each term variable.
- A variable contributes 1 at its position and 0 elsewhere.
- Application combines function usage with argument usage scaled by the
  function binder quantity: usage(f) + q * usage(argument).
- A lambda checks the usage of its bound variable, then returns the remaining
  usage vector for its closure.
- Binder 0 requires observed computational usage 0.
- Binder 1 requires observed usage exactly 1.
- Unrestricted binders permit any observed coefficient.

Quantity.idr implements coefficient arithmetic and this local binder policy.
It also implements a finite alternative-permission join and its local admission
identity. This alone does not implement term/context checking, cubical branch
accounting, erasure, or normalization.

Type annotations and types must be checked in a separate erased judgment:
references there do not consume runtime resources. The exact judgment and its
interaction with dependence and substitution must be specified before coding
the checker. Checking annotations twice must not accidentally count two uses.

An erased argument still needs checking. Erasure never licenses arbitrary
untyped terms. Conversely, a runtime term must not extract erased information.

## Erased and runtime-relevant judgments

Proposed judgments are mode-indexed, following ATKEY18 §2:

    Gamma |- term : type @ mode => usage

Mode is erased (coefficient 0) or runtime-relevant (coefficient 1); omega is
a binder coefficient, not a third judgment mode.

- Type formation and annotations use erased mode and must consume zero runtime
  resources. They still require full typing and conversion checking.
- Variable usage is the mode coefficient at that variable's position.
- A lambda's bound-variable expectation is modeCoefficient * binderQuantity.
  Runtime mode enforces the local 0/exact-one/unrestricted policy; erased mode
  expects zero computational use. The remaining vector describes outer capture.
- Application combines function usage with binder-scaled argument usage. The
  argument is checked erased when the surrounding mode is erased or the binder
  quantity is 0; otherwise it is checked runtime-relevant.
- Conversion compares types in erased mode. No runtime resource use should arise
  merely from inspecting types.
- An erased term cannot be promoted to runtime mode without rechecking.

These are proposed algorithmic requirements, not a completed derivation of QTT.
The unrestricted local policy permits fewer observed uses; its relationship to
the full subusage/context rules must be justified. Closure duplication must scale
captured usage at the point of use; checking the lambda binder alone is not enough.

### Implemented accounting helpers

Usage.idr provides scope-length-indexed vectors, zero usage, pointwise addition,
scaling, variable usage, and local binder discharge with structured mismatch data.
Matching vector lengths do not establish matching context types. Discharge checks
only the newest coefficient, not whether the remaining vector is zero in erased
mode. A future checker must establish that invariant for the entire judgment.

There is intentionally no syntax-only usage traversal: application requires the
inferred function type to determine its argument coefficient. Cubical alternatives
and face systems need separately justified accounting, not blind addition.

## Required negative tests

- Discarding a linear binder in a computational body.
- Duplicating a linear variable.
- Returning an erased variable at runtime.
- Capturing a linear value in a closure and then duplicating that closure.
- Out-of-scope indices, including in annotations.
- Self-application through an inconsistent universe rule.
- A looping definition admitted as evidence of Void.

Some tests require later syntax; record them now rather than pretending they
are already executable.

## Cubical gate

Do not extend the ordinary application formula blindly to paths, composition,
or Glue. Specify separately:

- Which dimension operations are computationally erased.
- How boundary checking avoids falsely consuming resources multiple times.
- How composition systems account for overlapping and disjoint faces.
- How substitution and reduction preserve exact use.
- Which transport computations remain after erasure.

Until those obligations are addressed, describe this work as an experimental
ordinary quantitative fragment beside cubical infrastructure, not a finished
quantitative cubical kernel.

## Implemented syntax layer

`src/Fibril/Core/Term.idr` implements the grammar with Fin-indexed variables,
renaming, weakening, simultaneous capture-avoiding substitution, and newest-binder
instantiation. Domain annotations remain outside the newly introduced binder.
Lifting a substitution weakens its replacements and preserves the bound variable.
Structural equality is deliberately distinct from conversion; these terms need
not be well typed, terminating, or quantity-correct merely because they are scoped.

Regression tests cover identity operations, weakening/instantiation, capture
avoidance, binder-domain scope, and structural-versus-computational equality.
[Renaming](renaming.md) now proves identity, composition, pointwise congruence,
and weakening commutation for every current scoped term in Idris 2.
[Substitution](substitution.md) now also proves identity, pointwise congruence,
and correspondence with variable-only substitution.
[Composition laws](substitution-composition.md) prove full structural substitution
composition, both mixed fusion laws, and weakening/instantiation identities.
These host-checked syntax results do not establish
typed/quantitative preservation or a combined calculus.

See [ordinary checking plan](ordinary-checking.md) for context formation,
dependent lookup, proposed rules, and explicit conversion/subusage gates.
Context.idr now implements telescope storage and whole-vector local validation,
not context well-formedness or inference.

## Immediate next task

Refine context formation, subusage, and erased/runtime rules into a complete
checking specification before implementing bidirectional checking. Usage-vector
helpers, an erased ordinary checker, and an experimental ordinary runtime-usage
checker now exist. The local subusage policy and preservation obligations remain
unresolved; see [runtime checking](runtime-checker.md). An evaluator for arbitrary scoped terms
must not claim total normalization: scoped syntax still admits divergent terms.
