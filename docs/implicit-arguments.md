# Explicitly declared implicit arguments

## Use cases

**Implemented first slice:** a named-module global may declare one leading erased
implicit parameter. Its first ordinary argument can determine that parameter:

~~~fibril
keep : {0 A : Type} -> (1 value : A) -> A
keep T item = item

message : String
message = keep "receipt"       -- proposes A = String
other : String
other = keep {String} "explicit"
~~~

The equation still names **both** parameters, in signature order. `{0 A : Type}`
means the parameter is both implicit *and* erased; `(0 A : Type)` remains erased
but **explicit**, and existing calls of the form `keep String value` retain
their meaning for such signatures. Braces at a call site provide the omitted
argument explicitly; they are distinct from dictionary requests like `@{}`.

The [runnable qualified-import example](../examples/modules/implicit-arguments/Main.fib)
uses inferred and explicit arguments, including a phantom parameter that must be
supplied explicitly. From the compiler project:

~~~sh
fibril run --source-dir examples/modules/implicit-arguments examples/modules/implicit-arguments/Main.fib
~~~

It prints `queued: receipt`, `explicit type`, and `phantom type`. These are
strings, not an email queue. The same example can be emitted by the experimental
[native console backend](native-c.md). This feature is source convenience over
explicit core `Pi`/`Apply`, not a new core type rule or a general unifier.

![Implicit argument elaboration](diagrams/implicit-arguments.svg)

## Supported boundary

- Only **one leading `{0 name : type}`** in a named-module global's authored
  signature is supported; it must be followed by a literal ordinary explicit Pi.
  Non-erased implicit binders, multiple implicit binders, implicit binders later
  in a telescope, and implicit data/record header parameters are rejected.
- Insertion applies only to a **direct visible global head** at its first
  ordinary argument: `keep value` or `Utility.Identity.keep value`. Qualified
  checked direct imports preserve the declaration's visibility metadata.
  Local shadowing takes precedence. Standalone declaration files, local or
  higher-order function values, infix operators and aliases without their own
  implicit signature do not get automatic insertion. A bare `keep` is a
  reference to the whole function, not an automatically instantiated value.
- The elaborator synthesizes the first ordinary argument's type and structurally
  matches it against the next Pi domain with a scoped unknown for the implicit
  parameter. It handles direct variables, supported structural type constructors
  and nominal indices/shapes when their syntax matches. Solutions may refer to
  variables in the caller's context, but may not escape a locally opened binder.
  A repeated constraint must agree under guarded comparison.
- All omitted information must be determined **from that one argument**. A
  phantom parameter, conflicting constraints, a type computation that requires
  unavailable normalization, an argument whose type cannot be synthesized,
  or an exhausted budget fails rather than inventing a solution. Use, for
  example, `label {Bool} "text"`. This slice does not postpone unknowns across
  later arguments or solve from the surrounding result type. It cannot yet make
  `Left "hello"` infer a phantom second parameter.

The metadata records authored visibility; it is not a type certificate. The
module driver checks that it corresponds to an erased leading core Pi followed
by an explicit Pi, and installs it only after checking the declaration. The
proposed solution is checked against the implicit domain, and ordinary core
checking and runtime usage analysis independently validate the **complete**
application and enclosing declaration. No metavariable or implicit Pi enters
core syntax. An erased argument must still obey erased-stage restrictions; an
inferred argument cannot authorize extracting erased data or duplicating a
linear value.

## Bounds, tooling and evidence

For automatic insertion, the checked function type, synthesized argument type
and proposed solution are admitted at 512 raw core nodes each; module preflight
reserves space for the type clone and inserted argument before global expansion.
Matching is structural and uses guarded equality for repeated solutions. The
existing erased checker synthesizes the authored argument's type **before** its
result-size check and may perform fuel-limited reduction and intermediate
substitution. Consequently these policies are not an end-to-end bound on
allocation, stack, time, or intermediate term size. Failure or inconclusive
comparison is not a proof of type inequality.

The formatter retains braces and verifies the re-parsed shape. Definitions and
references use authored binder and argument tokens; no source location is invented
for an inferred term. Project-aware rename is still unavailable. Tests cover
qualified imports, outer type variables, nominal types, explicit phantom fallback,
shadowing, malformed syntax, ambiguity, conflicting and escaping constraints,
erased/linear misuse, resource rejection and the native backend. These tests
are sampled implementation evidence, not proofs of solver completeness,
erasure or whole-language soundness.
