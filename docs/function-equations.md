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
Separate, narrowly bounded structural forms for Nat, unary recursive data and
the list shape are described below; none proves whole-language totality.

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
general recursive definitions and termination checking are not added. Small
structural Nat, unary-data and list-shaped equations are the exceptions below. Keep using
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
four marks after doubling two. A second [example](../examples/modules/recursive-render/Main.fib)
recursively constructs a String. The compiler accepts one named linear Nat
argument and a result type independent of that argument, with exactly one
`Zero` arm and one `Succ k` arm in either order. The zero arm cannot use the
function or either bound name. The successor arm must contain **exactly one
direct call** `f k` on the immediate predecessor. Calls on the original input,
a successor, a different value, or multiple recursive calls are rejected.

Branch expressions support ordinary references, literals, applications and
conditionals; binders, annotations, nested cases and implicit-brace applications
are not yet admitted in these branches. A call in only one conditional branch
may still be rejected by independent linear-usage checking. The predecessor may
appear only as the argument of the recursive call, not as a runtime value.
Binder and global-name collisions are not silently reinterpreted. The special
syntax is only accepted when the built-in `Zero` and `Succ` are visible without
shadowing; qualified aliases remain ordinary names, not evidence of recursion.

This syntactic admission constructs a closed core `NatRec`, whose step has an
erased predecessor and a linear previous result. Independent core typing and
usage checking remain authoritative. Unchecked signature normalization is
size/payload guarded, and an inconclusive or exhausted attempt does not accept
recursion. This is **not** a general termination checker: additional parameters,
binder-containing successor expressions, multiple recursive calls, mutual
recursion and dependent results need later work. Use explicit [`natRec` or `natRecWith`](nat-recursion.md) for operations
outside this narrow source form. Experimental C emission supports these checked
Nat forms, subject to its own runtime limits.

After project checking, definition navigation resolves accepted structural
self-calls using the actual authored name token and definition span. Same-file
rename/references do not yet infer recursive bindings. Formatting retains the
authored case and validates its shape.

## Structural unary-data equations

The same restricted style works for the fixed unary recursive shape, including
visible constructors from direct imports:

~~~fibril
marks : (1 chain : Chain) -> String
marks chain = case chain of
  Empty => ""
  More rest => appendString "!" (marks rest)
~~~

The [recursive-data example](../examples/modules/recursive-data/Main.fib)
compares direct one-step matching, a named fold and this equation form. No named
eliminator is required for the equation. The signature has exactly one named
linear input and a result independent of that input; the case has one terminal
and one unary-tail arm, in either order. The successor body admits exactly one
unqualified direct call on its immediate tail. As for Nat, the tail cannot
otherwise be used, and branch expressions are limited to the binder-free subset
above. An ordinary non-recursive direct case still works without this lowering.

The compiler checks visible, unrestricted constructor globals against the
canonical constructors for the exact inferred family under guarded conversion;
spelling, declaration order and authored schema metadata are not authority.
Transparent aliases may match. It lowers the admitted equation to a `RecFold`
with an erased tail and linear induction result; independent core type and usage
checks still validate the whole function. This is convenient syntax for the
existing fixed-shape fold, not general recursive equations, positivity or a
termination checker. Checked project definition navigation uses a self-call
site recorded only when lowering succeeds. Experimental C emission supports this
checked fixed-shape fold, subject to native limits.

## Structural list-shaped equations

For a fixed list-shaped family, a structural equation can use both the head
and the recursive result:

~~~fibril
join : (1 items : Items String) -> String
join items = case items of
  Empty => ""
  Prepend head tail => appendString head (join tail)
~~~

The [recursive-list example](../examples/modules/recursive-list/Main.fib) uses
qualified constructors from a direct import. As with unary equations, there
must be one terminal and one successor arm in either order, no explicit motive,
and exactly one direct self-call on the immediate tail. The head and tail names
must be distinct and referenceable. The head is linear; the tail may only occur
as the argument to that recursive call. A base expression cannot reference the
input or function. The same binder-free expression whitelist applies.

The compiler shares the guarded, checked constructor comparison used by direct
list cases, including checking an erased parameter's domain before applying the
actual element type. The equation lowers to `SeqFold` with a linear head, erased
tail and linear induction result, and is independently checked. A named fold
is not required. The result must be input-independent. One leading erased `Type 0` parameter is
also supported when the list element is exactly that parameter:

~~~fibril
copy : {0 A : Type} -> (1 items : Items A) -> Items A
copy Element items = case items of
  Empty => Empty {Element}
  Prepend head tail => Prepend head (copy tail)
~~~

The [polymorphic example](../examples/modules/polymorphic-recursion/Main.fib)
uses the actual erased parameter in a dependent result. For an implicit prefix,
`copy tail` or `copy {Element} tail` keeps that parameter fixed; with an explicit
`(0 A : Type)` prefix, use `copy Element tail`. The equation header names both
parameters. A separate, fixed map-shaped form supports two leading implicit
`Type 0` parameters and one unrestricted transformer:

~~~fibril
mapItems : {0 A : Type} -> {0 B : Type} ->
  (transform : (1 value : A) -> B) -> (1 items : Items A) -> Items B
mapItems A B transform items = case items of
  Empty => Empty {B}
  Prepend head tail => Prepend (transform head) (mapItems {A} {B} transform tail)
~~~

The [mapping example](../examples/modules/polymorphic-map/Main.fib) runs under
both the reference and experimental C runtimes. Its recursive call must spell
both type arguments and pass the **same** type parameters and transformer,
followed by the immediate tail; omission, reordered or changed arguments are not
inferred as equal. The transformer is unrestricted because the fold step can
execute repeatedly; a linear transformer cannot be captured. The admitted
signature is exactly the same list family at `A` to that family at `B`, with a
linear-element transformer. This is convenience over a checked fold, not a
general termination checker.

Other multiple-parameter telescopes, dependent results over the input, arbitrary
recursive calls and general termination checking remain unsupported. Checked project definition navigation
resolves the authored self-call; experimental C emission supports the checked
fixed-shape fold subject to native limits.

## Bounds, tooling and evidence

The existing expression parser budget limits equation header arguments. A
parameter's elaborated domain is admitted at 512 raw core nodes before it is
copied into the generated lambda. Module checking reserves 513 nodes per binder,
plus signature/body expansion, before cloning globals. The recursive forms reserve
additional admitted result-type copies and branch expansion before construction;
list equations also reserve for the head, tail and induction-result binders;
the existing cumulative
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
