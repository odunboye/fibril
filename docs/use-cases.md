# Feature use cases: which tool should I reach for?

Start with the problem, not the syntax. Features below are implemented prototype
slices, not promises of a complete Idris replacement. Follow the linked contracts
for supported syntax, checking boundaries and resource limits.

## Values, functions and resources

| Feature | Use it to… | Prefer something simpler when… |
| --- | --- | --- |
| [String](strings.md) | Represent text; append or compare it through ordinary functions. | You only need a yes/no decision: use Bool. |
| [Bool and conditionals](boolean.md) | Choose between two computations while checking branch resource use. | There is no decision to make; call the function directly. |
| [Unit](unit.md) | Represent completion or an intentionally uninformative result, such as console output. | A meaningful result exists; return that value instead. |
| [Typed functions and declarations](declarations.md) | Name reusable operations and expose independently checked signatures. | A small one-off expression or local let is sufficient. |
| Dependent function types | Describe a result whose type depends on an argument, or a function generic over a type. See [declarations](declarations.md). | Input and output types do not depend on values; use an ordinary function signature. |
| [Quantity 0](runtime-checker.md) | Pass type/index information needed for checking but unavailable for runtime use. | The computation must inspect or return the information at runtime. |
| [Quantity 1](runtime-checker.md) | Require an input to be consumed exactly once, including through branches. | Dropping or repeated use is intentional; use unrestricted permission. This is not yet a file/socket ownership library. |
| [Unrestricted permission](runtime-checker.md) | Allow an input to be discarded or used repeatedly, such as an operation dictionary shared across calls. | Exactly-once use is part of the contract. |
| [Universes](core-draft.md) | Give types and type families appropriate levels, including records containing types. | Working only with ordinary values; do not raise levels arbitrarily to hide an error. |
| [Type annotations and local bindings](declarations.md) | State an intended type, name an intermediate value, or clarify a checking boundary. | Direct application already expresses the computation clearly. |

## Data and dependent patterns

| Feature | Use it to… | Simpler alternative / limitation |
| --- | --- | --- |
| [Named records](records.md) | Package related fields behind an authored constructor and declared telescope. | Keep separate arguments if no reusable data shape is needed. Records are structural, not nominal class tags. |
| [Dependent fields](records.md) | Package a type/index and a payload whose type depends on it, or a request type and response family. | Use independent fields when there is no dependency. |
| [Non-recursive data](data.md) | Express Optional/Result-style choices with checked named constructors and an optional consuming eliminator; constructors may carry dependent fields. | Use records when every field is present. Direct data case syntax, recursive Nat/List and termination checking remain future work. |
| [Singleton records](unary-records.md) | Give a one-field package the same construction/pattern workflow as other records, without dummy Unit padding. | Use the field directly when the wrapper adds no useful abstraction. |
| [Erased record parameters](records.md) | Reuse one record definition across element types or indices without treating those parameters as runtime data. | A fixed concrete record is enough. |
| [Requested getters](records.md) | Access one field when the checker permits discarding the others. | Destructure and consume the package when other fields are linear. Not every field admits a safe getter. |
| [Optional named eliminators](records.md) | Request a reusable consuming helper, especially for a wider record. | Omit the helper if current patterns/getters already cover your uses. |
| [Typed patterns and motive inference](pattern-inference.md) | Consume a unary/binary package and compute a result, including supported dependent results. | A safe getter suffices. Use an explicit return motive when inference cannot establish the dependency within its bounds. |
| [Constructor-named patterns](constructor-patterns.md) | Make the intended packing visible and avoid spelling the underlying Box/Sigma shape. | Typed structural patterns already communicate enough. This is not multi-constructor discrimination. |
| [Inferred pattern fields](constructor-patterns.md) | Omit repeated field domains and quantities that the checked constructor already determines. | Keep typed binders when clarification or the bounded inference fallback is needed. |
| [Inferred erased pattern parameters](pattern-parameters.md) | Avoid repeating recoverable type/index arguments in a case pattern. | Supply parameters explicitly when phantom/noninvertible information cannot be recovered. |

## Generic operations: why dictionaries?

For ordinary string concatenation, write:

~~~fibril
appendString "Hello, " "world!"
~~~

Use a dictionary when an algorithm should depend on an operation rather than a
specific built-in function. For example, a generic concatThree can combine three
values using a supplied Semigroup operation; the caller chooses the element type
and behaviour. Calling that method for String can look like:

~~~fibril
combine String @{implementation} "Hello, " "world!"
~~~

Here combine is the generated method, String is its erased type argument,
@{implementation} requests a unique visible named dictionary, and the final two
arguments are the inputs. If the selected dictionary uses appendString, the
result is "Hello, world!". The dictionary layer buys reusable generic code—not
better string concatenation, automatic associativity evidence or a new primitive.

| Feature | Use it to… | Prefer / beware |
| --- | --- | --- |
| [Interfaces](explicit-interfaces.md) | Describe related operations required by a generic algorithm. | Use ordinary functions for a single concrete task, or records for different field permissions. Interface names do not certify algebraic laws. |
| [Named implementations](explicit-interfaces.md) | Give a concrete checked operation dictionary a reusable name; make alternative behaviours explicit. | A direct function argument is enough if no shared dictionary is needed. |
| [Named method blocks](implementation-blocks.md) | Build a dictionary by method name instead of remembering constructor field order. | Use an explicit constructor expression for aliases, plain records or an unavailable schema. |
| [Explicit implementation factories](implementation-factories.md) | Reuse a wrapper's implementation across element types by supplying the element operations, e.g. Semigroup A to Semigroup (Box A). | An ordinary function returning a dictionary also works; factories are not recursively discovered by lookup. |
| [Named constraints](constraints.md) | Show that a function needs a dictionary supplied by its caller. | Hardcode a concrete operation only when the function is intentionally not generic. |
| [Explicit selection: @{ops}](constraints.md) | Choose a particular dictionary, including when alternatives coexist. | A unique local request is less repetitive when intent remains clear. |
| [Local selection: @{}](constraints.md) | Reuse the unique matching dictionary already in a generic function's local context. | Name the dictionary if local selection is ambiguous. It never searches globals. |
| [Visible lookup: @{implementation}](visible-implementations.md) | Select the unique matching checked named implementation at a concrete call site. | Use an explicit name when behaviour should stay pinned as imports change. No recursive factory search occurs. |
| [Named infix calls](infix.md) | Read a two-input operation between its operands: left `appendString` right. | Prefix application is clearer for long type/dictionary arguments or non-binary functions. Chains group left; that is not an associativity proof. |

Runnable progression: [explicit dictionaries](../examples/modules/interfaces/Main.fib),
[named method blocks](../examples/modules/interface-blocks/Main.fib),
[local constraints](../examples/modules/constraints/Main.fib),
[visible lookup](../examples/modules/visible-implementations/Main.fib),
[backtick calls](../examples/modules/infix/Main.fib).

## Programs and tooling

| Feature | Use it to… | Boundary / alternative |
| --- | --- | --- |
| [Local workspace planning](workspaces.md) | Plan separately owned email/UI/platform libraries with deterministic package order and explicit direct dependencies. | Planner is an internal API; strict manifest inspection is separate. Workspace check/run is not implemented. Use current single-root modules for runnable projects. |
| [Manifest inspection](manifests.md) | Validate local email/UI package metadata without traversing paths or running hooks. | Schema-only; no source checking, resolved dependencies or locks. Prefer explicit source roots for runnable projects. |
| [Project creation](project-creation.md) | Start a runnable console source tree with `fibril new NAME`, or preview it with --dry-run. | Existing-directory init and generated manifests are not implemented; use explicit check/run commands. No hooks or dependency fetching occur. |
| [Modules, imports and exports](modules.md) | Split reusable definitions across files and publish a deliberate API. | Use one file for a small experiment. Only checked direct imports grant visibility. |
| [Erased globals](modules.md) | Publish type abbreviations or other checking-only definitions without granting runtime access. | Use an unrestricted value if runtime computation needs it. |
| [IO descriptions and do notation](console-runner.md) | Describe console actions and sequence results through typed bindings. | Keep pure computation outside IO; describing/evaluating a plan is not executing it. |
| [check / eval / run](cli.md) | Validate a program, inspect bounded reduction, or execute an admitted console plan, respectively. | Do not use run merely to find out whether a program typechecks. |
| [elaborate](elaboration.md) | Inspect generated named IR while debugging surface syntax and lowering. | Use check for acceptance: elaborate output is explicitly unchecked. |
| [Unicode source validation](unicode-source.md) | Reject malformed UTF-8/control characters before parsing or applying source-aware edits. | Valid encoding does not imply a valid or checked program. |
| [Resource admission](safety-performance.md) | Reject inputs/expansions beyond explicit compiler work policies before expensive construction. | Limits are not timing, stack, allocation or sandbox guarantees. |
| [Diagnostics](diagnostics.md) | Find a source-backed failure location and checking stage; consume JSON from tools. | A declaration anchor is not an exact failing-subexpression location. |
| [Definitions, references and rename](editor-highlighting.md) | Explore authored names and preview supported lexical edits. | Inspect manually when project-wide references/rename are required; those are not implemented. |
| [Source formatting](formatting.md) | Make layout consistent, including unsaved editor buffers, while retaining guarded syntax/trivia. | It is not a rewrite/refactoring tool, automatic save or universal line-width guarantee. |
| [Offline handbook](handbook.md) | Read language contracts, examples and source links without a network connection. | API reference alone is better for looking up an exact host declaration. |

## Application target: transactional email

The [transactional-email plan](applications/transactional-email.md) drives an
application-readiness milestone: durable authenticated submission, a remote TLS
relay and a responsive web/mobile console. Its [first runnable Fibril model](../examples/modules/email-service/Main.fib)
checks submission transitions and rejects blind dispatch after acknowledgement
loss. It is not a network service, C deployment, delivered-email guarantee or
completed UI; the plan identifies the backend/runtime blockers explicitly.

## Implementation/research features are not language promises

[De Morgan interval/face machinery](foundation-baseline.md) supports experiments
and tests toward a future cubical checker; users cannot yet write checked general
path/cubical programs. Structural host proofs explain specific scope/substitution
operations, not complete language soundness or verified erasure. [Benchmarks](benchmarks.md)
help compare measured workloads, not establish universal performance bounds.

The [internal finite-variant kernel](finite-variants.md) now provides checked
nullary/payload alternatives and dependent cases for compiler development and
host tests. Source data now reaches it through checked declarations and helpers.

[Closed nominal wrappers](nominal-data.md) now distinguish equal-shaped internal
data and preserve phantom arguments. They now back checked source data while
leaving structural record identity unchanged.

[Checked declaration construction](data-declarations.md) now gives a future
frontend an all-or-error bundle of checked closed type/constructor definitions,
qualified keys and ordinary layout metadata, with cumulative admission. It is
still an internal API alongside the named-IR source elaborator. Direct source
matching, rather than authored declarations, remains pending.

[Non-recursive source data](data.md) now exposes finite choices and named
elimination, with an [Optional/dependent-package example](../examples/modules/data/Main.fib).
The [inductive-data plan](inductive-data.md) still separates direct source cases,
recursive Nat/List, positivity and termination from those implemented features.

Recursive inductive data, recursive instance construction, symbolic fixities,
checked equality/path terms and native/web/embedded backends remain future work.
Do not choose an implemented feature on the assumption that those already exist.
