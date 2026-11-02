# Named constraints and local dictionary selection

**Implemented prototype:** a named constraint is a dictionary-shaped parameter,
and dictionary applications can request explicit or unique local selection.
There is no global instance search, anonymous constraint insertion, subclass
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
global/coherent instance lookup, defaults/inheritance and generic operators need
separate scope, ambiguity, resource and reproducibility policies.
