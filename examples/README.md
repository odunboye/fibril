# Examples

The [512-bind native stress fixture](core/binary-many-binds.fib) exercises the
binary continuation stack. Its compiled native execution succeeds; the hosted
default currently exhausts reduction fuel. See [runtime scalability](../docs/binary-runtime-scalability.md).

The [binary frame library/client](modules/binary-frame/Main.fib) parses and echoes
one canonical Content-Length frame with a 0..4096-byte body, entirely in Fibril.
Use explicit binary `--source-dir` execution/emission; see [framing](../docs/binary-framing.md).

The [binary chunk echo](core/binary-echo.fib) and [bounded sequence echo](core/binary-echo-loop.fib)
require explicit hosted `fibril run-binary` or native `emit-c-binary`. They
preserve arbitrary bytes through stdio; the separate framing example supplies a
small canonical Content-Length layer.
Native binary C links `fibril_binary_runtime.c`, not the legacy runtime alone.

The [UTF-8 bytes example](core/utf8-bytes.fib) explicitly handles encoding and
decoding outcomes, with hosted/native text output. It does not grant binary IO.

The [pure bytes example](core/bytes-pure.fib) constructs a NUL octet, appends
another byte and computes length. It performs no binary IO; use `fibril eval`.
The [native pure bytes example](core/bytes-native.fib) feeds a byte-derived length
into text output and supports checked C emission; it is not binary transport.
The [byte ranges example](core/bytes-ranges.fib) uses truncating slice and explicit
missing/found indexing in both hosted and compiled execution.

Strict YAML inspection fixtures live in [manifests/](manifests/README.md). They are
not executable workspace projects or source-checking examples.

The [request-api package](packages/request-api/src/Mail/Request.fib) models
three pure email-service request alternatives, with a [separate test
package](packages/request-api/test/src/RequestTests/Main.fib). It does not send
mail or validate addresses. Run `fibril test --package examples/packages/request-api/fibril.yaml`.

The [multi-field-case example](modules/multi-field-case/Main.fib) matches two- and
four-field constructors directly with `case`, binding every field.

The [motive-do example](modules/motive-do/Main.fib) uses a dependent match in
a typed do-let without an explicit return motive.

The [motive-contexts example](modules/motive-contexts/Main.fib) exercises nested
and arbitrary-scrutinee motive inference.

The [implicit-arguments example](modules/implicit-arguments/Main.fib) exercises
inferred, partially explicit and explicitly supplied erased parameters through a checked import. The [implicit-constraints example](modules/implicit-constraints/Main.fib) also uses an expected result; [implicit constructors](modules/implicit-constructors/Main.fib) opt a data header into the same convenience. The [Nat recursion example](modules/nat-recursion/Main.fib) computes with an independently checked structural recursor; [Nat predecessor](modules/nat-predecessor/Main.fib) demonstrates runtime predecessor access with an unrestricted count, and [recursive equations](modules/recursive-equations/Main.fib) use the narrow checked Nat equation syntax, including a [String renderer](modules/recursive-render/Main.fib). The [recursive data example](modules/recursive-data/Main.fib) imports a unary recursive family and folds its actual tail; [recursive list](modules/recursive-list/Main.fib) carries linear elements through a parameterized fold; [linear accumulator](modules/linear-accumulator/Main.fib) reverses onto a changing linear accumulator via a direct equation lowered to a checked function-valued fold, with a [computed update](modules/linear-accumulator/Decorated.fib) a [distinct String accumulator](modules/linear-accumulator/StringAccumulator.fib), a [computed Bool result](modules/linear-accumulator/Matches.fib), an [accumulator-first equation](modules/linear-accumulator/AccumulatorFirst.fib), and a [uniform-prefix version](modules/linear-accumulator/UniformPrefix.fib); [polymorphic recursion](modules/polymorphic-recursion/Main.fib) copies a list using one erased element-type parameter; [polymorphic map](modules/polymorphic-map/Main.fib) uses two type parameters and a reusable transformer; [uniform recursion](modules/uniform-recursion/Main.fib) also carries an unchanged separator; [uniform Nat and chain](modules/uniform-nat-chain/Main.fib) reuse the same style across both unary shapes; [conditional recursion](modules/conditional-recursion/Main.fib) uses recursive calls in mutually exclusive alternatives.

The [mutual parity example](modules/mutual-parity/Main.fib) uses a bounded two-worker `mutual where` block compiled to ordinary Nat recursors, not general recursive-core or SCT admission. The [payload version](modules/mutual-parity/Payload.fib) carries an unchanged linear Bool through the same checked lowering. The [reordered version](modules/mutual-parity/Reordered.fib) eliminates one acyclic forwarding alias, preserving each member's Nat/Bool argument order.

The [function-equations example](modules/function-equations/Main.fib) combines
signature-derived named parameters with direct data cases.

The [bare Type example](modules/bare-type/Main.fib) uses Type for Type 0 in
expressions and data/record/interface headers while retaining explicit Type 1.

[Direct data cases](../docs/direct-data-cases.md) include executable generic Sum
and dependent-motive examples in modules/direct-data-case*. The separate
packages/sum-client imports packages/sum-library and directly matches its
qualified constructors via `fibril run --package examples/packages/sum-client/fibril.yaml`.

The standalone [sum-library](packages/sum-library/src/Data/Sum.fib) fixture
provides non-Church finite choices with a checked, ordinary fold and an authored
suite; direct source matching is separately available for local and qualified direct-imported zero/unary patterns.

The standalone packages/boolean-library fixture has no application entry; use
`fibril check --package examples/packages/boolean-library/fibril.yaml` and
`fibril test --package examples/packages/boolean-library/fibril.yaml`.
See [libraries and tests](../docs/libraries-and-tests.md).

A real two-package check/run example is in packages/{mailer,email-core}:
`fibril run --package examples/packages/mailer/fibril.yaml` (from the compiler root).
It calls a checked Fibril email-label function from the separate local library;
see [local package boundaries](../docs/local-packages.md).

## Runnable bootstrap project (Idris 2)

These programs use Idris 2 and the current Fibril implementation library.
They are **not source programs compiled by Fibril**. The Checking example invokes
Fibril's experimental erased and runtime-usage checkers on explicitly constructed core terms.

From the repository root:

```sh
pack build fibril-examples
pack run fibril-examples
```

Progression:

1. `src/Examples/Basics.idr`: hello-world text and linear identity.
2. `src/Examples/Proofs.idr`: length-indexed vectors, arithmetic induction,
   and list induction. Proofs are checked by Idris 2.
3. `src/Examples/Cubical.idr`: structural proof of interval-substitution
   identity, symbolic De Morgan equality, and face constraints.
4. `src/Examples/Checking.idr`: validate a polymorphic identity with both experimental erased and runtime-usage core checkers.
5. `src/Main.idr`: executable combining the examples; failed checks exit nonzero.

The structural proof is about interval syntax. Boolean equality checks do not
constitute a proof of solver correctness or implement univalence.

## Minimal source input

`core/identity.fib` is a checked annotated-expression source example.
Run `./build/exec/fibril check examples/core/identity.fib` from the root.
Use `lex-source` instead of `check` to inspect tokens. This is not yet a full module
or compiled program. `identity-unicode.fib` checks the same expression using
λ/⇒, and `identity-type.fib` checks its dependent function type with `--erased`.
`universe-lift.fib` exercises upward literal-universe compatibility.
`evaluate-identity.fib` runs through checked reference evaluation with `fibril eval`.
`make examples` checks the four checking examples and evaluates this fifth source
example as well as running the Idris project. It also checks
`identity-annotated.fib`, which states an explicit dependent type using an ascription.
`local-identity.fib` demonstrates a typed linear let and is evaluated by
`make examples` too. `unit.fib` evaluates a checked local Unit value, the
first ordinary data primitive; this remains reference evaluation, not compiled IO.
`consume-unit.fib` explicitly eliminates a linear Unit with case/of and is also
evaluated by `make examples`. `boolean.fib` defines linear negation using a
conditional and evaluates to True. Both alternatives are checked before evaluation.
`branch-permissions.fib` retains the former branch-equality counterexample; it now
normalizes and passes post-reduction checking under unrestricted permissions.

`declarations.fib` and `declarations-polymorphic.fib` are now runnable program
files with explicit signature/definition pairs and a main entry. Both are included
in make examples. See [declaration rules and opacity limits](../docs/declarations.md).

`hello-world.fib` runs with `fibril run` using a checked Fibril putStrLn function.
make examples checks it without printing, then executes it. Complete IO semantics,
modules, and C/JS backends remain future work; see [IO functions](../docs/console-runner.md).

`console-sequence.fib` demonstrates a flat console do block. It validates all
output requests before execution and is run by make examples. This uses new
experimental core IO-description rules, not a complete effect calculus.

`string-identity.fib` uses first-class pure String values in ordinary declarations
and a linear function. make examples evaluates it to a quoted normal form; this
does not execute console printing.

`console-expressions.fib` prints results of pure closed String applications,
conditionals, and local bindings. All arguments are core-checked, reduced and
rechecked before the first output. File-level IO helpers are now supported.

`io-functions.fib` uses an ordinary helper and actual Fibril pure/bind/putStrLn
functions. Only run executes the IO description's prepared stdout requests.

`io-map.fib` transforms a write's Unit result to Bool using the ordinary Fibril
map function, then branches on it to produce a second write. Mapping preserves
output order and does not execute effects during checking/reference evaluation.

`do-bindings.fib` names String/Bool IO results with `(1 name : Type) <- action`.
Names scope over subsequent statements, are consumed exactly once, and lower to
existing core Bind. Unannotated bound blocks return IO Unit; do (B) checks a block returning IO B.

`do-let.fib` combines typed pure let statements with IO result bindings in one
block. Pure bindings retain ordinary quantities and do not execute descriptions.

`do-result.fib` uses an explicitly annotated do (String) block to return a String
from a helper, then consumes that result in main : IO Unit. The annotation is
checked using existing core IO rules; it does not perform effects or infer types.

`string-append.fib` composes pure appendString calls in a linear helper to print
a computed greeting. Concatenation is checked core computation, not parser syntax
or IO; its host allocation/copying costs are not bounded by reduction fuel.

`string-equal.fib` compares a computed String with equalString and branches on
the Boolean result to choose console output. Comparison is exact text equality,
not Unicode normalization or a dependent equality/path proof.

`boolean-library.fib` uses ordinary Fibril notBool/andBool/orBool functions with
String comparison to choose output. Binary operations consume both inputs once;
they are deliberately not conventional short-circuit operators.

## Module graph fixtures (discovery only)

`modules/graph/` forms a diamond dependency graph. Inspect it with:

~~~sh
./build/exec/fibril module-graph examples/modules/graph examples/modules/graph/Main.fib
~~~

This parses and loads snapshots only; JSON reports checked: false. No greeting
executes during discovery. Use explicit --source-dir commands for project
checking/evaluation/execution, not the headerless single-file path.

## Checked module examples (hosted execution)

`modules/checked/` contains a private helper and a qualified exported greeting.
Check it with:

~~~sh
./build/exec/fibril check --source-dir examples/modules/checked examples/modules/checked/Main.fib
~~~

This type/resource-checks all dependencies and the entry without printing. To run
it, replace check with run using the same --source-dir arguments: it prints
Hello, Fibril! Replace check with eval to display the inert IO description instead.
Project JSON/editor diagnostics are not wired yet.

## Explicit generic operations (not interfaces yet)

`modules/operations/` passes an operation and identity candidate explicitly across
module boundaries. The same Fibril combineThree function is instantiated at String
and Bool; text adapters bridge the existing linear wrapper to an unrestricted
operand profile. Run it with:

~~~sh
./build/exec/fibril run --source-dir examples/modules/operations examples/modules/operations/Main.fib
~~~

It prints Hello, Fibril! No interface syntax, dictionary records, implementation
search, or algebraic law proofs are claimed. See the
[interface design contract](../docs/interfaces.md) for staging/quantity decisions.

## Named dependent records (bounded source prototype)

`modules/records/` constructs an erased type/linear value package, recovers its
payload through dependent elimination, and consumes a two-field message. Run it:

~~~sh
./build/exec/fibril run --source-dir examples/modules/records examples/modules/records/Main.fib
~~~

It prints Records! Record types, constructors and explicit eliminators are
checked ordinary declarations after lowering. This first source grammar supports
exactly two single-line fields in a named module; it is structurally transparent,
not nominal. Projection functions require explicit safe requests; dot-field
syntax is not provided. Explicit erased parameters and
typed two-field consuming patterns are supported. See
[record foundations](../docs/records.md).

The alternate entry `modules/records/Patterns.fib` uses explicit consuming
patterns and dependent motives instead of named eliminator calls:

~~~sh
./build/exec/fibril run --source-dir examples/modules/records examples/modules/records/Patterns.fib
~~~

It prints Patterns! No inferred or constructor-discriminating pattern grammar
is claimed.

## Parameterized record dictionaries

`modules/record-parameters/` prints Record parameters! using an explicit generic
operation/identity record. It also checks rebuilding a dependent indexed record
whose second parameter is a type family over its first. Run with:

~~~sh
./build/exec/fibril run --source-dir examples/modules/record-parameters examples/modules/record-parameters/Main.fib
~~~

This is checked explicit record passing, not interface syntax, law checking,
implicit parameter inference or instance search. Constructors/eliminators take
erased parameters explicitly. See [record parameters](../docs/records.md#record-parameters).

## Safe record projections

`modules/record-projections/` combines a dependent payload getter with generic
operation/identity getters and prints Safe projections!:

~~~sh
./build/exec/fibril run --source-dir examples/modules/record-projections examples/modules/record-projections/Main.fib
~~~

Each getter consumes its record once. A request that discards a linear field or
extracts an erased field at runtime is rejected. Calls are ordinary functions,
not .field syntax. See [safe projection functions](../docs/records.md#safe-projection-functions).

## Proposed Fibril programs

`proposed/` illustrates the intended user experience, from hello world and
ordinary proofs to advanced computational univalence and application scenarios.
These files are explicitly **not executable**. The `.fib` suffix is provisional.
Do not present them as supported language features.

As Fibril becomes usable, migrate these scenarios into real compile/run and
expected-failure tests. Keep implementation status visible.
