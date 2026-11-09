# Named constraints and local dictionary selection

## Use cases

Use named constraints when one algorithm should work with caller-supplied operations rather than hardcoding a concrete implementation. For example, concatThree can combine three values of any supported type using its Semigroup dictionary.

Use `@{}` inside that function to avoid repeating its unique local dictionary name. Use `@{ops}` when several dictionaries are in scope or behaviour should be explicit. For a concrete string-only helper, `appendString` is usually simpler; constraints do not improve concatenation itself.

**Implemented prototype:** a named constraint is a dictionary-shaped parameter,
and dictionary applications can request explicit or unique local selection.
There is no automatic or recursive global instance search, anonymous constraint insertion, subclass
search, operator overloading or algebraic-law checking.

~~~fibril
concatThree : (0 A : Type 0) -> (ops : Semigroup A) =>
              (1 left : A) -> (1 middle : A) -> (1 right : A) -> A
concatThree = \(0 A : Type 0) => \(ops : Semigroup A) =>
  \(1 left : A) => \(1 middle : A) => \(1 right : A) =>
    combine A @{} (combine A @{} left middle) right
~~~

A definition still binds the dictionary with an ordinary explicitly typed
lambda. No expected-type-driven implicit lambda is inserted.

![Named constraint selection](diagrams/constraints.svg)

## Explicit requests, ordinary core terms

A named binder followed by => is a constraint Pi. Its quantity remains explicit
or the existing unrestricted default. It must have a structural Box/Sigma
dictionary domain and linear or unrestricted runtime permission. Erased proof
constraints are not part of this slice.

- function @{dictionary} supplies an explicitly selected dictionary.
- function @{} requests the unique matching visible local dictionary.
- @{implementation} separately opts into [visible named implementation lookup](visible-implementations.md).
- Ordinary explicit application function dictionary remains valid.

Both selection forms inspect the next function argument type, which must be a
runtime-permitted dictionary-shaped domain. Explicit arguments must match that
type. Automatic selection emits a single scoped variable, not a generated
dictionary or a copied value.

The elaborator lowers constraints to existing Pi and applications to existing
Apply. The kernel rechecks the original function, argument and quantities.
No core constructor, conversion rule, implicit coercion or trusted instance
certificate is introduced.

## Local selection policy

[Expression.Dictionary](../src/Fibril/Elaboration/Expression/Dictionary.idr)
examines the typed local context, not a global implementation registry:

1. Consider only lexically visible names; newer bindings hide older same-named
   bindings even if the newer one has a different type.
2. Exclude wildcard and erased bindings.
3. Compare dictionary-shaped types by bounded conversion.
4. Select only if exactly one candidate matches.
5. Report missing, ambiguous or inconclusive/exhausted selection as an error.

Ordinary typed dictionary parameters, lets and inferred pattern fields can be
candidates as well as named constraints. This is structural dictionary typing,
not nominal interface membership. A same-shaped record can match, and two
same-shaped but behaviorally different dictionaries are ambiguous.

Search does not use a resource ledger to choose between candidates. Reusing a
linear dictionary is still rejected by ordinary usage analysis; unrestricted
dictionaries can permit repeated calls. No borrowing or quantity weakening
occurs. An erased dictionary can still be mentioned by existing ordinary erased
program constructs, but cannot be revived as a runtime constraint argument.

## Inferred dictionaries after implicit arguments

A signature may put `=>` binders directly after a leading implicit prefix:

~~~fibril
both : {0 A : Type 0} -> (ops : Join A) => (left : A) -> (right : A) -> A
~~~

A call `both "a" "b"` first infers `A` from the arguments exactly as in
[implicit arguments](implicit-arguments.md); the constraint binders are skipped when
matching arguments to parameters. Each binder is then filled by lookup, in this order:

1. the unique matching lexically visible local dictionary (so generic code uses its own);
2. otherwise the unique visible named implementation (as `@{implementation}` does);
3. otherwise an error. Missing and ambiguous matches both fail with a source position and
   ask for an explicit `@{dictionary}`; there is no priority, default or recursive search.

Only binders directly after a non-empty implicit prefix are filled; the type argument is
what selects the dictionary. Functions without an implicit prefix keep their explicit
dictionary arguments, and `f {A} @{d} x` still supplies one by hand. The lookup result is
an ordinary applied argument, so the core checker validates it like any other term, and no
kernel rule, conversion rule or coherence guarantee is added. Uniqueness holds only among
the providers visible at that call: importing another instance can turn a call ambiguous.
See [the example](../examples/modules/inferred-constraints/Main.fib).

## Global calls remain explicit

[The example graph](../examples/modules/constraints/Main.fib) calls:

~~~fibril
Algebra.concatThree String @{Instances.Text.textSemigroup} "Hello" ", " "interfaces!"
~~~

Its generic [Algebra functions](../examples/modules/constraints/Algebra.fib)
select from their local dictionary binders. Merely importing an implementation
does not make it an automatic candidate. The entry's @{} would fail in an empty
local context even when an implementation global exists.

The example also exercises Bool/NAND and a two-method Monoid dictionary. It
prints Hello, interfaces!, Explicit dictionaries! and Monoid shape!.
These remain operation shapes, not associativity or identity proofs.

## Bounds, source services and evidence

Type exposure and comparisons use the current checker depth 512 and reduction
fuel 128. The source parser bounds argument chains. Lookup visits the finite
visible context, without recursive dictionary construction or backtracking.
Inconclusive candidates are not silently discarded to manufacture uniqueness.
These are work policies, not wall-clock/allocation guarantees.

Errors use the actual @{...} selection span and the elaboration stage.
Syntax-only tools retain constraint-pi and dictionary-apply nodes; elaborate
PATH remains explicitly unchecked and leaves local-unique requests pending.
No source token or definition target is invented for an automatically selected
argument. Explicit selection expressions retain normal lexical navigation.
Formatting preserves @{} / @{dictionary}, constraints and shape guards.
Vim/Neovim highlights the new punctuation.

Tests cover the imported generic graph, explicit and automatic calls, absent
global fallback, ambiguity/explicit disambiguation, exact selection points,
shadowing, erased exclusion, linear reuse rejection, malformed/non-dictionary
requests, formatter idempotence and explicit argument definition targets.

**Remaining:** anonymous constraints, implicit application insertion,
recursive/parameterized instance lookup, global coherence, defaults/inheritance and symbolic operators need
separate scope, ambiguity, resource and reproducibility policies.
[Named backtick infix calls](infix.md) now support ordinary constrained methods.
