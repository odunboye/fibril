# Explicit interfaces and named dictionary implementations

## Use cases

Use an interface to describe operations shared by a generic algorithm. A Semigroup dictionary supplies a combine operation; a Monoid shape additionally supplies an identity value. Implementations let String and Bool reuse the algorithm, or let callers explicitly choose different behaviours for one type.

For a one-off string append, call `appendString` directly. Use a plain record when the data needs different field permissions. An interface name is not a proof of associativity, identity laws or nominal membership.

**Implemented prototype:** interface declarations, generated checked method
functions, and explicitly typed named dictionary implementations. Dictionaries
are passed explicitly or selected by a [unique-local request](constraints.md).
Named constraints are supported; no automatic/recursive global instance search, inheritance, overloaded
operators, superclasses or law checking is implemented. Interface identity is [nominal](nominal-interfaces.md).
[Named method-body blocks](implementation-blocks.md) now provide schema-guided
constructor elaboration without instance search.

![Explicit dictionary pipeline](diagrams/explicit-interfaces.svg)

## Surface syntax

~~~fibril
export
interface Semigroup (0 A : Type 0) : Type 0 where
  constructor MkSemigroup
  eliminator useSemigroup
  combine : (1 left : A) -> (1 right : A) -> A

export
implementation textSemigroup : Semigroup String
textSemigroup = MkSemigroup String appendString
~~~

Headers follow the existing record layout: named module, explicit constructor
name, an optional eliminator name, erased parameters, a declared universe, and aligned
single-line method signatures. interface and implementation are now reserved
keywords. The implementation keyword shares its line with the signature;
the matching definition name starts in column one on the following definition
header. Export is a separate preceding line.

A method field must be unrestricted (omitted quantity). Its **argument**
quantities remain explicit and invariant: the example method consumes each
argument once. Constants such as a Monoid identity are supported too. Erased
law fields and linear method fields are not admitted in this first interface
slice; use explicit records for other permission shapes.

Each method automatically generates an ordinary consuming getter with the
method's authored name. A call is explicit:

~~~fibril
combine String textSemigroup "Hello" ", interfaces!"
~~~

It takes all erased interface parameters, then a quantity-1 dictionary, then
the method's own arguments. A linear dictionary cannot be used by two calls.
Use an explicitly unrestricted dictionary binder when reuse is intended.
No borrowing, hidden copying or quantity coercion is added.

Method names are ordinary module-level names and must be unique alongside other
declarations. Different interfaces in one module cannot overload the same
method spelling. Separate modules can qualify names normally. Explicit
projection directives are rejected inside interfaces: the methods already
supply the generated getter names.

## Genuine checked dictionaries, not registrations

The parser retains InterfaceItem and ImplementationItem authored declarations.
It does not generate expression bodies or perform instance lookup.
[Declaration elaboration](elaboration.md) lowers an interface through the same
checked record generator: a unary wrapper for one method, dependent Sigma
telescopes for multiple methods, and an independently checked getter per method.

An implementation can supply a **complete ordinary dictionary expression**,
or a [named method block](implementation-blocks.md) guided by a visible interface
schema. Neither form searches for missing methods. Checked named values are now eligible
for explicitly requested [visible implementation lookup](visible-implementations.md),
not automatic implicit application or recursive instance construction. The ordinary constructor checker
rejects missing fields, wrong method types and quantity mismatches.

The compiler independently requires implementation globals to be unrestricted
and their checked signature to expose a unary wrapper or dependent pair, or
an [explicit factory](implementation-factories.md) returning one after erased
and dictionary parameters. A primitive alias or arbitrary function is not enough. Interfaces are
[nominal](nominal-interfaces.md): an interface lowers to a one-constructor type whose key is its
module-qualified name, so a dictionary of one interface is never accepted for another. Plain
record dictionary aliases are still accepted by this gate; they are different types from any
interface and are never selected for an interface constraint.

Every private, unused, imported and generated body is checked before exports
are published or any IO plan executes. Checking uses the original bodies,
not normalized bodies that could erase staged resource failures. The
implementation marker adds no trusted axiom and no kernel term constructor.

## Example and law boundary

~~~sh
./build/exec/fibril run --source-dir examples/modules/interfaces examples/modules/interfaces/Main.fib
~~~

The [four-file example](../examples/modules/interfaces/Main.fib) defines
[Semigroup and Monoid shapes](../examples/modules/interfaces/Algebra.fib),
[String dictionaries](../examples/modules/interfaces/Instances/Text.fib) and
a [Boolean dictionary](../examples/modules/interfaces/Instances/Boolean.fib).
One generic concatThree function runs at String and Bool. withIdentity uses
two methods from an explicit reusable Monoid dictionary. Output:

~~~text
Hello, interfaces!
Explicit dictionaries!
Monoid shape!
~~~

The Boolean operation is deliberately nonassociative NAND. Its acceptance
demonstrates only that its operational type/quantity contract checks.
Associativity and identity laws are **not established** by the names Semigroup
or Monoid, by method shapes, or by a successful implementation check.
Propositional equality, law representation and calculational reasoning remain
separate foundational work.

Multiple named implementations of one interface at the same type are
allowed. Callers choose a value explicitly or request unique visible lookup; no coherence, preferred-instance,
ambiguity-resolution or algebraic-law guarantee follows.

## Tooling, admission and evidence

Authored binding sites include the interface type, explicit constructor,
optional named eliminator, and real method-name tokens. Generated method definitions navigate
to those tokens, not synthetic source. Implementation signature/definition
names retain ordinary navigation. Group export/private policy follows records.
Vim/Neovim highlights the new keywords; formatting preserves authored kinds and
handles implementation bodies using the guarded ordinary expression layout.

Each method getter consumes an ordinary declaration slot, in addition to the
two dictionary declarations (three if a named eliminator was requested). Existing source, parameter, 64-declaration,
cumulative generated-IR, expanded-core and checker budgets apply; no new fixed
method-count quota is introduced.

elaborate PATH remains explicitly unchecked. Its declaration JSON includes
an implementation boolean; it can inspect an unresolved or wrongly shaped
implementation target without certifying it. Checking separately rejects that
target. Raw DeclarationWithRole metadata is ordinary data, not a certificate.

Tests cover String/Bool generic calls, a two-method dictionary, explicit choice
between same-typed dictionaries, type/quantity failures and explicit adapters,
unsafe method quantities, private groups, unused bad implementations, automatic
getter origins, declaration budgets, formatting and execution after formatting
the imported graph. These are prototype tests, not a soundness theorem.

**Next:** global selection/coherence policies and generic operators.
Named method-value blocks, [local selection](constraints.md) and opt-in
[visible implementation lookup](visible-implementations.md) are implemented;
implicit/recursive global instance resolution is not. Bounded coherent search and operators come only
after visibility, ambiguity and quantity policies are specified.
