# 5. From representations to experimental checking

## Learning goals

Follow a checking request through context formation, erased inference,
conversion, and runtime usage validation.

![Selected calls](../diagrams/calls.svg)

This is a curated selected call graph, not an exhaustive dynamic execution trace.

## A source-to-core slice

The [expression frontend](../parser.md) now loads, lexes, parses named syntax,
and resolves lexical scopes before calling these checkers. The source
`examples/core/identity.fib` reaches the polymorphic identity below. Full
Idris-like declarations and implicit elaboration are not implemented.

## Erased checking first

[Erased](../../src/Fibril/Core/Erased.idr) exposes three operations:

1. checkErasedContext: validate telescope domains in preceding contexts.
2. inferErased: validate the context, then infer a term's ordinary type.
3. checkErased: also validate the expected type and compare it with inference.

Internal inference assumes the context has been checked; it is not public.

### Follow polymorphic identity

Using the term from chapter 2:

- The outer domain Universe 0 has type Universe 1.
- Extending with A makes the inner domain Variable FZ a type.
- Extending with x lets its body infer A at the correctly shifted index.
- The two inferred function layers reconstruct the expected Pi type.

Universes are stratified: Type l : Type (l+1). No Type : Type is allowed.
Literal universe compatibility now permits checking upwards without making
levels definitionally equal; [the plan](../cumulativity-rewriting.md) explains
why this is not general function subtyping. Pi levels take the maximum of domain/codomain levels.

### Compatibility is not equality

[Compatibility](../../src/Fibril/Core/Compatibility.idr) accepts normalized
Universe i at Universe j when i <= j. Other types still require equal normal
forms. betaCompare remains exact; Pi domains, quantities, and codomains do not
silently coerce. Dependent rewriting remains future transport-based work.

### Application

Infer the function, normalize its type to expose Pi, check the argument's inferred
type against the domain, then substitute the argument into the codomain.
No admitted holes or arbitrary axioms fill failed obligations.

## State the expected type in source

Use `(expression : expectedType)` to make an obligation explicit. The
[annotated identity example](../../examples/core/identity-annotated.fib) checks
a polymorphic function against its dependent Pi type. The resolver inserts a
linear identity application, so existing checking enforces the obligation without
an unchecked cast or a new kernel rule. See [ascriptions](../parser.md#explicit-type-ascriptions).

## Add runtime accounting

[Runtime](../../src/Fibril/Core/Runtime.idr) reuses erased typing, then runs a
type-directed usage pass:

- Variables contribute singleton usage.
- Lambdas discharge bound-variable use and retain captured usage.
- Application scales the argument by its inferred binder quantity.
- Erased arguments contribute zero use but were already fully type checked.
- Completed usage is checked against the ambient context.

Direct Universe/Pi values are unsupported computational expressions. The module
checks resource policy; it is not a C/JavaScript runtime.

## Diagnostics and limits

Typing-depth and reduction budgets fail explicitly. Resource mismatches distinguish
local binders from ambient variable indices. Diagnostics do not yet carry source
locations because core-to-source diagnostic mapping has not yet been implemented,
even though the expression parser/resolver retains frontend spans.

Repeated context checks make this a reference implementation, not an optimized
incremental elaborator. Prefer correctness and clear boundaries before caching.

## Exercise

Find “runtime duplicated closure captures rejected.” Trace which captured entry
becomes omega and where validateUsage rejects it.

**Read:** [erased checker](../erased-checker.md), [runtime checker](../runtime-checker.md).
**Boundary:** these ordinary prototypes do not implement cubical term checking,
and local usage-policy preservation is not formally established.
