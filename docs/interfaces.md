# Interfaces: explicit operations before search

**Status:** design contract plus runnable higher-order Fibril examples. Interface,
implementation, record, implicit dictionary, and operator syntax are **not
implemented**. Nothing here establishes associativity, identity laws, quantitative
soundness, or a computational HoTT equality theory.

The [module boundary](modules.md) is now executable. We should use it to build
reusable abstractions instead of permanently growing a monomorphic prelude.
This page records the next implementation order and its outstanding checks.

![Implementation order and current boundary](diagrams/interfaces.svg)

## What works now

The four-file [operations example](../examples/modules/operations/Main.fib) runs:

~~~sh
./build/exec/fibril run --source-dir examples/modules/operations examples/modules/operations/Main.fib
~~~

It prints Hello, Fibril! through an ordinary checked IO description. The generic
[Algebra.Operation](../examples/modules/operations/Algebra/Operation.fib) defines
combineThree and surround using explicit operation parameters. Independent
[Text](../examples/modules/operations/Instances/Text.fib) and
[Boolean](../examples/modules/operations/Instances/Boolean.fib) modules supply
operations and identity **candidates**. Main uses the same combineThree at String
and Bool; the generic module contains no String/Bool special cases.

The important method shape is ordinary Fibril:

~~~fibril
combineThree : (0 A : Type 0) -> (combine : (left : A) -> (right : A) -> A) -> (left : A) -> (middle : A) -> (right : A) -> A
combineThree = \(0 A : Type 0) => \(combine : (left : A) -> (right : A) -> A) => \(left : A) => \(middle : A) => \(right : A) => combine (combine left middle) right
~~~

This is **not yet a dictionary record or an interface instance**: the operation
and identity are separate explicit arguments. The small example makes quantity
and module decisions observable without parser-special functions or simulated
compilation. Its type parameter is small (Type 0), not universe-polymorphic.

surround computes combine identity (combine value identity). The checker does
not conclude that the result equals value. The identity candidate is data, not
a law witness. Tests of selected strings/Booleans are examples, not proofs of a
universal algebraic law.

## Quantities are part of the method contract

Conventional Semigroup operations may duplicate or discard operands. For example,
left-biased selection can be associative while ignoring its second operand.
We must not silently require every such operation to consume each operand once.

The first operational profile will therefore use unrestricted operands. Its
dictionary/method argument is also unrestricted, allowing generic code to invoke
it repeatedly. This profile is not appropriate for consuming linear resources.
A separate linear operation profile can be designed later; it is not an implicit
coercion or a promise that all algebraic interfaces share one resource policy.

The current prelude appendString and andBool consume their operands once.
Their Pi types are not convertible to unrestricted-operand Pi types. The
example deliberately defines explicit adapters:

~~~fibril
append : (left : String) -> (right : String) -> String
append = \(left : String) => \(right : String) => appendString left right
~~~

This uses existing checking rules: unrestricted binders permit one use. It does
not change Pi conversion, discard a linear capture, or grant an unrestricted
caller access to a linear variable. Passing appendString directly where the
unrestricted profile is expected must remain rejected.

An implicit method-quantity coercion would be a new feature with its own design,
elaboration and resource tests, not a shortcut in instance selection.

## First prerequisite: erased global type declarations

The current module compiler accepts unrestricted globals only. Separately, the
runtime checker rejects runtime type expressions. Therefore an unrestricted
AppendOperation returning a Pi type is **not** a supported workaround for naming
the operation shape. A named quantity-0 global is also currently rejected.
The runnable example writes the method type explicitly rather than weakening
that boundary or pretending a type declaration was accepted.

Before interface/record types, implement a checked erased-global boundary:

1. Preserve declaration quantity/stage in global metadata and lookup.
2. Check erased definitions in the erased judgment; runtime declarations still
   require runtime checking. Validate signatures before publication.
3. Permit erased names in types and erased arguments, but reject their use as
   runtime values, including ordinary erased Bool/String definitions. Do not
   special-case names that happen to normalize to types.
4. Preserve this restriction across imports, signature ascriptions, alias chains,
   source order, and exported interfaces. Never normalize away the original
   occurrence before checking whether that occurrence is permitted.
5. Extend admission cost accounting before cloning new wrappers/metadata. Test
   rejection before effects and keep source diagnostics honest.

A Boolean erased global is a necessary negative test: checking an erased body
then inserting its raw closed value as an unrestricted global would lose the
stage restriction. Closedness alone is not permission to resurrect erased data.
The public metadata structures themselves are not certificates.

The existing headerless local-let opacity contract is independent; adding erased
named module declarations must not silently change local typed-let semantics.

## Second prerequisite: dictionary representation

Choose a small, explicit record or dependent-product representation before
surface interface syntax. Specify formation, introduction, elimination,
computation, conversion, and quantitative usage together. Record metadata must
not be a side table that installs unchecked core values.

For the initial conventional profile, dictionaries are ordinary explicitly
passed reusable values with unrestricted method fields. A linear dictionary
must not expose projections that discard other linear fields or duplicate
linear captures. Dependent field types and erased proof fields need a clear
elaboration order; they cannot be added merely as unchecked parser metadata.

Every new core constructor must update full/head reduction, scope operations,
resource checking, pretty-printing, structural host proofs, generators, and
regression tests. Host substitution proofs still are not a subject-reduction
proof. Decide whether record eta is definitional before relying on it; do not
silently inherit all Idris record rules.

## Explicit implementations before inference

The first interface lowering should produce ordinary dictionary types,
constructors, and method access. Callers pass dictionaries explicitly. Modules
export the checked interface signature and selected implementations through the
existing private-default/direct-import boundary.

Proposed semantic obligations, not implemented syntax:

- A Semigroup-shaped dictionary supplies a binary method with a declared quantity
  profile. String append is one candidate implementation.
- A Monoid-shaped dictionary supplies that operation plus an identity candidate;
  String uses the empty string. Dictionary composition/superinterfaces must not
  accidentally copy linear fields.
- Dictionary introduction checks each method against its published signature.
  Method dispatch is ordinary core computation, not parsing an operation name.
- An interface name is not an associativity certificate. Until equality and law
  representation exist, describe any operational interface as law-unchecked.
  equalString returns Bool, not a dependent equality/path proof.

Only after explicit lowering is stable should constrained functions and coherent
implementation lookup be added. Multiple explicit dictionaries for one carrier
are useful and unambiguous; global uniqueness is not required for explicit use.
Future inference must define candidate visibility, ambiguity, local overrides,
overlap, superinterface search, and termination budgets before enabling search.
No implicit filesystem/network lookup, initialization hooks, or orphan-instance
loading is introduced by interface resolution.

Generic operators follow ordinary method resolution after that phase. Migrate
concrete wrappers compatibly rather than adding parser-special String operators.
Keep the low-level primitive boundary distinct from library abstraction.

## Evidence and acceptance gates

Current evidence consists of the checked String/Bool program, explicit quantity
adaptation, negative signature/resource cases, and the existing module/IO tests.
There is no record elaborator, dictionary inference, law proof, benchmark claim,
or soundness theorem in this slice.

Implementation order:

1. Staged erased globals and their import/runtime rejection tests.
2. Minimal checked dictionary representation and all affected core infrastructure.
3. Explicit operational interfaces and implementations, including failed methods.
4. Law representation once equality supports it; distinguish data from proofs.
5. Constrained functions, bounded/coherent lookup, then generic operators.

This order keeps failures local and avoids committing to surface syntax before
its core and resource meaning is known.
