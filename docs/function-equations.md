# Named function equations

## Use cases

**Implemented:** give a previously signed function ordinary parameter names on
its definition line instead of repeating explicit lambdas and type annotations.
For example, a request renderer can name its inputs while retaining their
quantities in the signature:

~~~fibril
render : (1 prefix : String) -> (1 request : Request) -> String
render prefix request = case request of
  Health => prefix
  Preview subject => appendString prefix subject
~~~

The [runnable example](../examples/modules/function-equations/Main.fib) also
shows a dependent identity whose definition names differ from the names in its
signature. Run:

~~~sh
fibril run --source-dir examples/modules/function-equations examples/modules/function-equations/Main.fib
~~~

Use explicit lambdas when writing anonymous functions, when annotations on the
body are more readable, or when the signature is not an explicit Pi telescope.
Ordinary named equations are elaboration convenience over existing core lambdas.
A separate, narrowly bounded structural Nat-recursion form is described below;
neither form constitutes a proof of whole-language totality.

![Function equation checking](diagrams/function-equations.svg)

## Meaning and restrictions

~~~fibril
identity : (0 A : Type) -> (1 value : A) -> A
identity T item = item
~~~

The elaborator reads each parameter's domain and quantity from the corresponding
explicit Pi in the declared signature and constructs ordinary core lambdas. The
signature's `A` and the equation's `T` need not have the same spelling: the
dependent codomain is already scoped under the preceding binder. The ordinary
core checker independently checks the whole resulting value against its declared
signature. Thus `T` is erased and `item` is linear; using an erased input at
runtime or duplicating/discarding a linear input is rejected just as with an
explicit lambda. A plain `A -> B` has the existing unrestricted quantity.

The first slice requires a signature followed by **one** definition equation.
Parameters are bare names or `_`, occupy the definition header line, and are
unique except for wildcard `_`. **Every bare name, including an uppercase name,
is a binder—not a constructor pattern.** `_` does not grant permission to discard
a linear input. Nested constructor patterns, multiple clauses, guards, inferred signatures,
general recursive definitions and termination checking are not added. A small
structural Nat equation is the exception described below. Keep using
[direct data cases](direct-data-cases.md) in the body for existing nonrecursive
data matching; constant and supported expected-dependent motives can be [inferred](data-motive-inference.md). Imported qualified function calls retain ordinary visibility rules.

Fewer named parameters than explicit Pis are allowed: the body must itself supply
the remaining function value and still check. More names than Pis fail at the
authored offending name. A parameter can shadow an outer name under the existing
lexical scope rules; duplicate names within one header are rejected.

The elaborated signature must expose a **literal Pi** for each named parameter.
A type synonym or a beta-redex that would reduce to a Pi is deliberately rejected
by ordinary equations. This avoids reducing an unchecked signature merely to guess
binders; use an explicit lambda/annotation or write the Pi in the signature.
The narrow structural Nat form below instead uses size-guarded conversion and
also accepts a type alias when that conversion succeeds.
Explicit constraints are represented by ordinary Pis after their existing checks;
this feature does not add dictionary search. A module signature can also declare
[a leading erased implicit prefix](implicit-arguments.md); its equation still
names those parameters explicitly.

## Structural Nat equations

A named-module global can use this first recursive form:

~~~fibril
double : (1 n : Nat) -> Nat
double n = case n of
  Zero => Zero
  Succ k => Succ (Succ (double k))
~~~

The [runnable example](../examples/modules/recursive-equations/Main.fib) prints
four marks after doubling two. The compiler accepts one named linear Nat
argument and a Nat result, with exactly one `Zero` arm and one `Succ k` arm in
either order. The zero body must be `Zero` wrapped in zero or more `Succ`s. The
successor body must be **exactly one call** `double k`, wrapped in zero or more
`Succ`s. `k` is the immediate predecessor; calls on the original input, a
successor, a different value, or multiple recursive calls are rejected. Binder
and global-name collisions are not silently reinterpreted. The special syntax is
only accepted when the built-in `Zero` and `Succ` are visible without shadowing;
qualified aliases remain ordinary names, not evidence of recursion.

This syntactic admission constructs a closed core `NatRec`, whose step has an
erased predecessor and a linear previous result. Independent core typing and
usage checking remain authoritative. Unchecked signature normalization is
size/payload guarded, and an inconclusive or exhausted attempt does not accept
recursion. This is **not** a general termination checker: additional parameters,
String results, arbitrary successor expressions, multiple recursive calls,
mutual recursion, dependent results and user-defined recursive types need later
work. Use explicit [`natRec` or `natRecWith`](nat-recursion.md) for operations
outside this narrow source form. C emission still rejects Nat computation.

Project definition navigation resolves this exact self-call in import-free
modules with an unshadowed built-in Nat signature; other self-call navigation
is not yet supported. Same-file rename/references do not infer recursive
bindings. Formatting retains the authored case and validates its shape.

## Bounds, tooling and evidence

The existing expression parser budget limits equation header arguments. A
parameter's elaborated domain is admitted at 512 raw core nodes before it is
copied into the generated lambda. Module checking reserves 513 nodes per binder,
plus signature/body expansion, before cloning globals; the existing cumulative
200000-node construction budget and independent post-count still apply. These
are work-admission policies, not proofs of bounded memory or execution time.

Definition/reference/rename queries use the actual authored equation-parameter
tokens, including in unsaved buffers. The signature's copied elaboration input
is not presented as an invented second source use. The formatter preserves the
equation and verifies the re-parsed shape; `elaborate` remains unchecked named IR.

Tests cover dependent renamed binders, ordinary/erased/linear quantities,
excess/duplicate parameters, invalid patterns and multiple clauses, accidental
recursion, an unchecked redex-headed signature, source navigation/rename,
formatting and a runnable direct-data-case example. These tests are evidence of
this implementation, not a proof of metatheory or automatic termination.
