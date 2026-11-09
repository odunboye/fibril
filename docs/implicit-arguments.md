# Erased implicit arguments

## Use cases

**Implemented:** a named-module global may declare a leading prefix of erased
implicit parameters. Fibril can gather constraints from ordinary argument types
and, when available, from the expected result of the complete call:

~~~fibril
selectFirst : {0 A : Type} -> {0 B : Type} -> (1 left : A) -> (right : B) -> A
selectFirst T U left right = left

message : String
message = selectFirst "receipt" True       -- A = String, B = Bool
explicit : String
explicit = selectFirst {String} {Bool} "receipt" True
partial : String
partial = selectFirst {String} "receipt" True
~~~

The equation still names **all** parameters in signature order. `{0 A : Type}`
means implicit *and* erased; `(0 A : Type)` is erased but remains **explicit**.
Braces at a call site supply arguments positionally and precede ordinary
arguments. They are distinct from dictionary requests such as `@{}`.

The [qualified-import example](../examples/modules/implicit-arguments/Main.fib)
uses inference, explicit braces, partial braces and a phantom-parameter fallback.
The [expected-result example](../examples/modules/implicit-constraints/Main.fib)
solves an otherwise unknown `B` for `inject "receipt"` from the declared
`Sum String Bool` result. Run from the compiler project:

~~~sh
fibril run --source-dir examples/modules/implicit-arguments examples/modules/implicit-arguments/Main.fib
fibril run --source-dir examples/modules/implicit-constraints examples/modules/implicit-constraints/Main.fib
~~~

The first example can also be emitted by the experimental [native console
backend](native-c.md). Its output labels a request; it is not an email queue.
Implicit insertion is source convenience over explicit core `Pi`/`Apply`, not a
new core type rule or a complete unifier.

![Implicit argument elaboration](diagrams/implicit-arguments.svg)

## Supported boundary

- An authored module-global signature may have a consecutive leading prefix of
  `{0 name : type}` binders followed by a literal ordinary Pi. Generated
  constructors can also have an implicit-only prefix when they have no fields;
  their nullary application requires explicit braces. The inference
  telescope admits at most 64 implicit binders and 64 pending ordinary arguments
  before the prefix is solved. Non-erased implicit binders and implicit binders
  later in a telescope are rejected.
- Insertion applies to a **direct visible global head**: `f x y` or
  `Module.f x y`. Checked direct imports and explicit local package edges carry
  the visibility metadata. Local shadowing takes precedence. Standalone
  declaration files, local/higher-order function values, infix operators and
  aliases without their own implicit signature do not get automatic insertion.
  A bare global remains uninstantiated. Brace-only partial applications retain
  only their explicitly supplied core arguments; a new alias does not inherit
  implicit visibility automatically.
- The solver opens the erased prefix as elaborator-only scoped unknowns. It
  gathers structural constraints from a bounded type proposal for each ordinary
  argument; if its form has no supported type proposal, that particular
  constraint is skipped and later arguments or the final expected result can
  still solve the prefix. Exhausted depth, size or work admissions instead fail
  and request explicit arguments. Scope pruning rejects solutions that escape binders;
  repeated solutions must agree under guarded comparison. Once all slots are
  solved, remaining arguments receive the ordinary expected-domain treatment.
- The expected type, when available, constrains **the complete authored call**,
  never an intermediate partial call. The matcher handles supported structural
  types and nominal identities/indices/shapes. It does not normalize arbitrary
  type computations to discover solutions or perform higher-order unification.
  Earlier ordinary argument *values* are not substituted into later constraints;
  if a needed constraint depends on such a value, use explicit braces.
- A truly phantom, conflicting or ambiguous slot is not guessed. For example,
  `selectFirst {String} {Bool} "receipt" True` supplies both parameters. A
  data header with braces can opt constructors into the same inference, so
  `Left "receipt"` may use its expected `Choice String Bool` result. Headers
  with parentheses retain explicit constructor parameters, and record headers
  remain explicit. A nullary constructor needs e.g. `None {String}`: a bare
  `None` is not instantiated from an expected type. Explicit braces remain the
  fallback for unsupported argument forms or exhausted admissions. See
  [source data](data.md) for the opt-in syntax and its family/eliminator boundary.

The checked global's visibility metadata guides elaboration; it is not a type
certificate. The module driver validates the prefix against erased core Pis and
installs it only after checking the declaration. Solutions and authored values
become ordinary `Apply` terms; no metavariable or implicit Pi enters core syntax.
The ordinary core and runtime checkers independently validate the complete term,
including implicit-domain types, erased-stage restrictions and linear use.

An implicit prefix may be followed by `=>` constraint binders, which a call fills by
dictionary lookup after the prefix is solved; see
[inferred dictionaries](constraints.md#inferred-dictionaries-after-implicit-arguments).

## Bounds, tooling and evidence

When inference is needed, the checked function type and each proposed
argument/result type are admitted at 512 raw core nodes and 8192 aggregate
characters. A type proposal has depth 16,
and local type lookup admits at most 64 context entries. The solver has a
262144-unit structural-input metric shared across constraints.
These estimates are admissions, not a proof of total work: repeated guarded
conversion, host String-length measurement and other existing checker operations
have their own behavior. Sequential dependent implicit-domain substitutions are
estimated for node and character expansion **before** constructing each type;
the combined implicit solutions are limited to 512 nodes and 8192 characters.
Module preflight reserves the checked-type clone, implicit substitutions and
argument-type proposals before global expansion. Complete declarations are
independently rechecked. None of these policies proves bounded allocation,
stack, wall-clock time, erasure or whole-language soundness.

The formatter retains braces and verifies the re-parsed shape. Navigation uses
actual authored binder and argument tokens; inferred terms do not acquire fake
source locations. Project-aware rename remains unavailable. Tests exercise
qualified imports, opt-in data constructors, partial/explicit braces, multiple
arguments, expected-result constraints, dependent implicit domains, scoped variables, unresolved and
conflicting slots, staging and usage rejection, admission/fallback, and native
emission. They are sampled implementation evidence, not proofs of completeness.
