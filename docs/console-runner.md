# Fibril IO functions and hosted execution

Status: ordinary checked Fibril library functions over experimental core IO
descriptions. The old name-special-casing console parser has been removed.
Execution is still hosted; there is no C/JS backend or complete effect calculus.

## putStrLn is now a Fibril definition

[stdlib/Prelude.fib](../stdlib/Prelude.fib) contains:

~~~fib
putStrLn : (1 text : String) -> IO Unit
putStrLn = \(1 text : String) => primWriteLine text
~~~

The same file defines pure, bind, and map. These definitions are parsed, resolved, and
core-checked before becoming available through an implicit bundled prelude.
putStrLn is not a primitive name or a parser pattern. Local declarations can
shadow it, and helpers can call it through ordinary function application.

~~~fib
announce : (1 message : String) -> IO Unit
announce = \(1 message : String) => putStrLn message

main : IO Unit
main = bind String Unit (pure String "This is a Fibril library function.")
         (\(1 message : String) => announce message)
~~~

Run [that example](../examples/core/io-functions.fib):

~~~sh
./build/exec/fibril run examples/core/io-functions.fib
./build/exec/fibril run examples/core/hello-world.fib
~~~

The final primitive write still uses [host stdout](../src/Fibril/Runtime/Console.idr).
A standard-library function ultimately calling an OS/host primitive is expected;
the removed shortcut was treating its *name* as print syntax.

## Mapping an IO result in Fibril

The prelude's map takes explicit small types A/B, a linear pure function
transform : (1 value : A) -> B, and an action : IO A, returning IO B.
Its implementation is ordinary Fibril:

~~~fib
map : (0 A : Type 0) -> (0 B : Type 0) -> (1 transform : (1 value : A) -> B) -> (1 action : IO A) -> IO B
map = \(0 A : Type 0) => \(0 B : Type 0) => \(1 transform : (1 value : A) -> B) => \(1 action : IO A) => bind A B action (\(1 value : A) => pure B (transform value))
~~~

There is no map primitive or special typing/reduction rule. Its function argument
is used once, and that function must consume its result parameter once. Mapping a
Unit result therefore uses explicit Unit elimination rather than silent discard.
The action still describes its original writes before supplying the mapped result.

[io-map.fib](../examples/core/io-map.fib) maps a write's Unit result to Bool, then
uses that Bool to choose a second write. check validates it without printing;
eval displays the inert description; run prints the two lines in order.

If B itself is IO C, the result is IO (IO C), not IO C. map does not implicitly
flatten descriptions or execute a returned action. Use an explicit bind to pass
that description to a continuation. Runtime input remains unimplemented.

Tests cover identity/composition examples, ordering, captured linear values,
discard/duplication rejection, invariant function quantities, and explicit nested
IO handling. These finite regressions are not a proof of functor or monad laws.

## Core IO descriptions

The ordinary Term datatype now contains:

- IOType A, formed at the same universe level as A.
- IOPure value, of type IOType A when value has type A.
- IOBind A B action next, where action : IO A and
  next : (1 value : A) -> IO B, producing IO B.
- WriteLine text, requiring String and producing IO Unit.

IOType is a type expression, not runtime data. Runtime usage for Pure and
WriteLine is the operand's usage. Bind adds action and continuation usage; the
continuation's result parameter is exact-once. Inputs/outputs of bind are
nondependent; dependent motives are not provided.

The source primitive table exposes IO, primPure, primBind, and primWriteLine.
The current source/prelude interface quantifies A/B : Type0 only. The core IOType
formation rule does not collapse higher universes or introduce Type : Type.

The only new computation rule is a **pure description** rule:

    IOBind A B (IOPure value) next --> Apply next value

Reference normalization also computes inside descriptions, but WriteLine never
calls stdout there. There is no run/unsafePerformIO primitive in the core.

## check, eval, and run are different

- check uses ordinary runtime typing/resource checking, including IO programs.
- check --erased can check an IO description, but grants no runtime permissions.
- eval may normalize and display a description such as WriteLine "Hello"; it
  does not perform the write.
- run requires a runtime-checked IO Unit program and prepares a complete output
  plan before performing any host writes.

An IO A description is not evidence of A. In particular, a write request cannot
check as a Unit proof just because execution will eventually return Unit.
Erased extraction and linear discard remain rejected when run checks the program.

## do notation

~~~fib
main : IO Unit
main = do
  putStrLn "first"
  putStrLn "second"
~~~

do is now ordinary expression syntax, not part of a separate console entry
parser. Flat action lines are aligned, indented beyond column one, and each
action expression fits on one source line. Comments and blank lines are allowed.
At most 64 statements are accepted per block, counting both bindings and bare
actions; empty/nested blocks are not implemented.

Sequencing lowers to core Bind over Unit, with a linear continuation that
explicitly consumes the previous Unit through UnitCase. No returned linear
value is silently dropped.

Typed result bindings are also supported:

~~~fib
main : IO Unit
main = do
  (1 message : String) <- pure String "A named result."
  putStrLn message
~~~

The explicit type and quantity 1 are required. A binding introduces its name only
in subsequent statements, not its annotation or action. Shadowing uses the old
binding on the right-hand side and the new binding afterwards. The bound result
must be consumed exactly once; Unit results need an explicit case if named.
A binding cannot be the final statement.

This syntax lowers to IOBind A Unit action (Lambda Linear A body), using the
same core rules as explicit bind; it adds no primitive or trusted inference.
Consequently blocks containing a result binding currently return IO Unit.
For other final result types, use explicit bind. Bare sequencing likewise requires
Unit intermediate results. General result inference, dependent bind, unannotated
bindings, and nested/multiline statements remain future work.

[do-bindings.fib](../examples/core/do-bindings.fib) demonstrates String and Bool
bindings, mixing named results with bare actions and consuming a mapped result.

Functions, local bindings, ordinary declaration files, and higher-order
applications can produce descriptions. User declaration values still have the
existing opaque-let semantics during checking; this is not a module/import
implementation or a general transparent user-definition environment.

## Planning and the effect boundary

[Driver.Console](../src/Fibril/Driver/Console.idr) checks main against IO Unit,
head-exposes descriptions, checks residual terms, and interprets them into pure
PrintLine requests. Pure returns supply values; binds feed checked values to
continuations. String operands are fully normalized and rechecked before output
data is accepted, and the final result must check and normalize to Unit.

Only after the entire plan succeeds does [Driver.Run](../src/Fibril/Driver/Run.idr)
invoke the host adapter. A late type/resource failure, unsupported residual,
or exhausted planning budget executes no output prefix. Actual output failures
can still be partial; previous writes are not rolled back.

Planning depth is 128; each head/pure reduction call has fuel 128; output plans
are capped at 64 writes. Core checking depth is 512 (headroom for elaborated
continuations/library wrappers), with type-reduction fuel 128. Source parsing
depth remains 256 and the file cap remains 65,536 bytes. These independent limits
are not total time, allocation, or real-time guarantees.

Only stdout is implemented, so all requests can currently be planned without
performing effects. Runtime input, nondeterministic actions, foreign results,
cancellation, and interactive bind execution need a different explicitly designed
runtime boundary. There is no shell evaluation, general FFI, or sandbox.

run reserves stdout for program output and reports failures on stderr. Represented
host-write errors stop the sequence; buffering/flush failures, signals, crashes,
and OS blocking are not a complete structured-error guarantee.

## Bundling and global resolution

[Source.Global](../src/Fibril/Source/Global.idr) stores closed definitions.
Lexical bindings take precedence; global values are scope-safely embedded into
the core, not installed as axioms. Only closed unrestricted prelude definitions
are accepted. User imports, package/module identities, and source maps for these
globals are future work.

The compiler embeds the actual Fibril prelude source in a generated Idris module,
so run works outside the repository without finding a library file at runtime.
After editing stdlib/Prelude.fib:

~~~sh
make prelude
make test
~~~

The generated module is committed. make build checks its source/hash consistency;
direct pack build uses the committed generated module, so regenerate first after
library edits. Prelude type errors reject source preparation, not admit unchecked
globals. No dependency install hooks or external packages were introduced.

## Evidence and remaining gaps

Core renaming/substitution proofs have cases for all new constructors. Tests check
primitive signatures, library compilation, shadowing, normal helpers, bind results,
universe levels, linear/erased failures, safe description evaluation, late-failure
output suppression, and portable prelude loading. Generated IO programs compare
plans before/after reference normalization without executing writes.

These are prototype typing rules, host syntax proofs, and sampled regressions—
not a completed quantitative IO semantics, typed subject-reduction theorem,
monad-law proof, correct-erasure proof, cubical IO integration, or backend.
