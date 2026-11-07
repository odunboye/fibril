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

Ordinary single equations require a signature followed by one definition.
Parameters are bare names or `_`, occupy the definition header line, and are
unique except for wildcard `_`. In a single equation every bare name, including
an uppercase name, is a binder, not a constructor pattern. `_` does not grant
permission to discard a linear input.

A named module also admits two or more consecutive column-one equations for the
same signature as a nonrecursive constructor-clause group. Each clause matches
exactly one argument with a flat, unqualified constructor and zero or one named
payload binder; the signature must expose a corresponding explicit Pi. The group lowers to the existing data case, so its constructor shape,
exhaustiveness, motive inference and linear usage remain subject to those case
rules. A lone constructor-looking equation remains an ordinary binder equation.
Nested patterns, wildcard payloads, multiple matched arguments, guards, local or
mutual clause groups, inferred signatures and general recursive clauses are not
supported. The conservative clause recursion check rejects the function's bare
name even in binder positions; qualified references such as `Other.f` are
ordinary references. Use [direct data cases](direct-data-cases.md) for forms
outside this slice. Small structural Nat, unary-data and list-shaped equations
are separate exceptions below, not general termination checking.

A bounded Nat catch-all is also supported: `f Zero = ...` followed by
`f item = ...`, where `item` is a previously unresolved lowercase name, binds
the entire successor value (and may be unused). Visible or ambiguous names are
resolved as constructors instead, and a catch-all before `Zero` is rejected.
The input must be unrestricted: reconstruction uses an unrestricted successor
predecessor. Explicit `Succ` patterns still require linear use of their named
predecessor. General catch-alls and wildcard patterns are not supported.

Same-file definition and references include every clause header and supported
constructor and payload occurrences. Rename is capture-checked and same-file
only, and currently rejects documents with module headers; named modules cannot
use rename preview. Checked project definition uses the existing project navigation
rules. Navigation cannot certify a final bare head as a checked binder: it does
not link that head or its binder uses and conservatively suppresses outer-name
references with the same spelling in that clause body, even when the head is a constructor.
Rename rejects changes from or to an ambiguous final head's spelling, but can
preview unrelated names subject to its usual lexical capture checks.
Formatting and other tooling do not acquire additional clause-specific semantics.

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
recursively constructs a String. The compiler accepts a named linear Nat
argument and a result type independent of that argument, with exactly one
`Zero` arm and one `Succ k` arm in either order. A bounded uniform telescope of
erased or unrestricted parameters may precede the Nat input, as described below.
The zero arm cannot use the function or the structural input. The successor arm
must contain a direct call on the immediate predecessor, such as `f k` or
`f prefix k`. Both alternatives of an `if` may contain such a call: they are
mutually exclusive. Calls that can occur together, or calls on the original
input, a successor or a different value, are rejected.

Branch expressions support ordinary references, literals, applications and
conditionals. Uniform-prefix equations also admit explicit brace applications;
binders, annotations and nested cases are not yet admitted in these branches. A call in only one conditional branch
is rejected for runtime-checked functions by independent linear-usage checking
when another path drops the induction result. Erased declarations are checked
at the erased stage instead. The predecessor may
appear only as the argument of the recursive call, not as a runtime value.
Binder and global-name collisions are not silently reinterpreted. The special
syntax is only accepted when the built-in `Zero` and `Succ` are visible without
shadowing; qualified aliases remain ordinary names, not evidence of recursion.

This syntactic admission constructs a closed core `NatRec`, whose step has an
erased predecessor and a linear previous result. Independent core typing and
usage checking remain authoritative. Unchecked signature normalization is
size/payload guarded, and an inconclusive or exhausted attempt does not accept
recursion. This is **not** a general termination checker: changing recursive
parameters, binder-containing successor expressions, multiple calls along the
same path, mutual recursion and results dependent on the recursive input need
later work in this form. Equations outside it fall through to
[general recursion](#general-recursion) when they have a size-change decrease; otherwise
use explicit [`natRec` or `natRecWith`](nat-recursion.md). Experimental C emission supports these checked
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
eliminator is required for the equation. The signature has one named linear recursive input and a result independent of
that input; the case has one terminal and one unary-tail arm, in either order.
Erased or unrestricted parameters may precede the input when passed uniformly
on every recursive call. The successor body admits unqualified direct calls on
its immediate tail, including one in each mutually exclusive conditional branch. As for Nat, the tail cannot
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
and direct self-calls only on the immediate tail. Calls in both mutually
exclusive conditional branches may share the induction result; calls on the
same execution path are rejected. The head and tail names must be distinct and referenceable. The head is linear; the tail may only occur
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
parameters. A bounded uniform-telescope form supports multiple erased and
unrestricted parameters before the linear list, including the familiar mapping
shape:

~~~fibril
mapItems : {0 A : Type} -> {0 B : Type} ->
  (transform : (1 value : A) -> B) -> (1 items : Items A) -> Items B
mapItems A B transform items = case items of
  Empty => Empty {B}
  Prepend head tail => Prepend (transform head) (mapItems {A} {B} transform tail)
~~~

The [mapping example](../examples/modules/polymorphic-map/Main.fib) runs under
both the reference and experimental C runtimes. The more general
[uniform-telescope example](../examples/modules/uniform-recursion/Main.fib)
uses a renderer and separator captured by the repeated fold step.

The [conditional-recursion example](../examples/modules/conditional-recursion/Main.fib)
exercises exclusive calls for Nat, unary data and lists. The rewriter admits
those syntactic alternatives; runtime-checked declarations must still pass the
independent branch-sensitive linear-use check. This is not a general path or
termination proof.

The uniform form admits up to **64 prefix binders** at quantity 0 or
unrestricted, followed by one linear Nat, unary-recursive or list input. Prefix
domains and the result may depend on earlier parameters; the result must not
depend on the recursive input. The [Nat and chain example](../examples/modules/uniform-nat-chain/Main.fib)
shows an erased type and reusable function as well as an imported unary family.
Every recursive call must spell **all** prefix arguments with their authored
implicit/explicit visibility and pass the same bound names in the same order,
followed by the immediate tail. Omitted, reordered or changed arguments are not
guessed equal. Prefix arguments captured by the repeated step must be erased or
unrestricted; a linear prefix is not accepted. This is convenience over a
checked fold, not a general termination checker. The earlier single-erased-type
form still permits its documented omitted implicit argument.

Dependent results over the input, arbitrary non-uniform recursive arguments,
arbitrary recursive calls are not accepted by this form (they fall through to
[general recursion](#general-recursion)); the particular linear accumulator form
below is an exception. Checked project
definition navigation resolves the authored self-call; experimental C emission
supports the checked fixed-shape fold subject to native limits.

## Linear list accumulator

A narrow direct-style reverse-onto equation is also supported, with the list
first:

~~~fibril
reverseOnto : (1 items : Items String) -> (1 acc : Items String) -> Items String
reverseOnto items acc = case items of
  Empty => acc
  Prepend head tail => reverseOnto tail (Prepend head acc)
~~~

The accumulator may instead come first, provided the recursive call preserves
that order:

~~~fibril
matchesFrom : (1 acc : String) -> (1 items : Items String) -> Bool
matchesFrom acc items = case items of
  Empty => equalString acc "cab"
  Prepend head tail => matchesFrom (appendString acc head) tail
~~~

The [runnable example](../examples/modules/linear-accumulator/Main.fib) uses
qualified imported constructors. After an optional uniform prefix, the
signature has exactly two linear inputs: a checked fixed list family and an
accumulator type. Its result type may differ from the accumulator; neither may
depend on the two linear inputs. The list family must also be independent of
the accumulator. These types may depend on earlier prefix parameters. The case
scrutinizes the list input. Its empty branch computes the result from the accumulator, and
the cons branch is exactly a direct self-call on the immediate tail and an
update, in the function's authored argument order. Branch order may be reversed. The
[computed-update example](../examples/modules/linear-accumulator/Decorated.fib)
transforms each head before adding it to a list accumulator; the
[String-accumulator example](../examples/modules/linear-accumulator/StringAccumulator.fib)
uses a different accumulator type from the input list. The
[computed-base example](../examples/modules/linear-accumulator/Matches.fib)
returns a `Bool` from a `String` accumulator; the
[accumulator-first example](../examples/modules/linear-accumulator/AccumulatorFirst.fib)
uses the other argument order. The [uniform-prefix examples](../examples/modules/linear-accumulator/UniformPrefix.fib)
show erased types and a reusable transformer, including the
[accumulator-first form](../examples/modules/linear-accumulator/UniformPrefixFirst.fib).

The base may use the accumulator and visible globals; the update may also use
the head. Both are bounded binder-free expressions of ordinary or braced
applications, `if`, references, and supported literals. Neither may refer to
the original input or recursive function; the update may not refer to the tail.
Qualified references whose final name collides with a forbidden name are also
conservatively rejected. Head and tail binders are not in scope in the empty
branch, so same-named globals there retain their ordinary meaning. Cases,
lambdas, lets, do blocks and other unlisted forms are rejected. Both authored
expressions are elaborated and independently checked: the base must consume
the linear accumulator, and the update must consume both linear head and
accumulator.

Up to 64 erased or unrestricted prefix parameters may precede the two linear
inputs. Leading implicit prefix parameters must be erased. Each recursive call
must explicitly repeat every prefix binder unchanged, in the authored order and
with its authored implicit or explicit visibility; omitted, reordered or
computed prefixes are not guessed equal. Prefix values captured by the repeated
step must satisfy the existing erased/unrestricted usage rules. Linear prefixes,
indirect calls, other recursive arguments and additional trailing parameters
remain unsupported.

The compiler lowers this shape to a `SeqFold` returning a linear
accumulator-to-result function. Its base computes the checked empty branch;
each step builds a function that applies the linear induction result to the
independently checked update. The original accumulator is not captured by the
repeatedly invoked step. The generated outer lambdas preserve the two-argument
shape before applying the fold. The whole generated core is independently checked for types and usage.
This is syntax over an expressible fold, **not general recursion or use of the
experimental size-change checker**. Case-constructor identity is checked, not
inferred from spelling; authored update applications must satisfy their own
ordinary types and implicit-argument rules. Experimental native emission remains
unverified.

## Bounds, tooling and evidence

The existing expression parser budget limits equation header arguments. A
parameter's elaborated domain is admitted at 512 raw core nodes before it is
copied into the generated lambda. Module checking reserves 513 nodes per binder,
plus signature/body expansion, before cloning globals. The recursive forms reserve
additional admitted result-type copies and branch expansion before construction;
uniform equations also reserve for payloads, induction-result binders and the
admitted prefix telescope;
the existing cumulative
200000-node construction budget and independent post-count still apply. These
are work-admission policies, not proofs of bounded memory or execution time.

Definition/reference/rename queries use the actual authored equation-parameter
tokens, including in unsaved buffers. The signature's copied elaboration input
is not presented as an invented second source use. The formatter preserves the
equation and verifies the re-parsed shape; `elaborate` remains unchecked named IR.

## General recursion

When none of the structural forms above applies and an equation refers to itself,
Fibril elaborates it as a `Fix` over its own name and checks it with the
[size-change gate](size-change-certificates.md#fix-admission). The structural
forms still run first and are unchanged.

~~~fibril
half : (1 n : Nat) -> Nat
half n = case n of
  Zero => Zero
  Succ a => case a of
    Zero => Zero
    Succ b => Succ (half b)
~~~

This steps down by two, which no single-step recursor expresses. It is accepted
because `b` is strictly smaller than `n`. The [swap example](../examples/modules/general-recursion/Swap.fib)
is accepted only because two calls together decrease. A call that rebuilds its
input is refused, naming the call:

~~~text
Recursion: no argument decreases: recursive call 1 of 1 passes nothing smaller than a parameter
~~~

Limits: only list, recursive-data and Nat case tails count as smaller, so
recursion on other data is refused. A visible global with the declaration's own
name, such as two ambiguous imports, blocks the fallback rather than being replaced
by a self reference. Because source `Succ p` patterns bind a linear predecessor,
recursion that passes it to an unrestricted parameter (for example Ackermann) is
refused by usage checking until unrestricted patterns exist. The fallback inherits
the general elaborator's pattern resolution, which resolves a `Zero` pattern to
the built-in constructor even when an identical `Zero` is imported. Mutual
recursion beyond the bounded Nat/Bool pairs, native C emission and navigation from
a call to its definition are not supported. Runnable examples:
[Half.fib](../examples/modules/general-recursion/Half.fib) and
[Chain.fib](../examples/modules/general-recursion/Chain.fib) (accepted), and
[Loop.fib](../examples/modules/general-recursion/Loop.fib) (refused).

Tests cover dependent renamed binders, ordinary/erased/linear quantities,
excess/duplicate parameters, invalid patterns and multiple clauses, accidental
recursion, an unchecked redex-headed signature, source navigation/rename,
formatting and a runnable direct-data-case example. These tests are evidence of
this implementation, not a proof of metatheory or automatic termination.
