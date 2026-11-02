# Declaration elaboration and inspection

**Implemented:** parsing and record elaboration are separate compiler stages.
This is an explicit, bounded declaration elaborator, not yet a full Idris-style
implicit/unification elaborator. Record field counts are resource-admitted, not
fixed at eight; [singletons](unary-records.md) use a checked unary core wrapper.

![Stages and trust boundaries](diagrams/elaboration.svg)

## Authored syntax is not generated IR

[Source.Declaration.Syntax](../src/Fibril/Source/Declaration/Syntax.idr) defines
authored ordinary/record declarations, parameters, fields and projection requests,
and explicit interface/implementation items, as well as the lowered named declaration IR. A parsed record retains its actual
tokens, quantities, field/domain expressions and source spans. It is not replaced
by constructor/getter expressions during document parsing. Named implementation
blocks likewise retain method values and actual tokens until schema-guided
elaboration.

[Source.Declaration](../src/Fibril/Source/Declaration.idr) handles grammar and
framing. It has **no dependency on the elaboration layer**. It still checks layout,
record/parameter/projection syntax bounds, authored binding-name collisions and
the 64 binding-site quota. Binding sites are source metadata, not generated
expression bodies.

[Source.Document](../src/Fibril/Source/Document.idr) stores authored declarations.
Document symbols and lexical/project navigation use authored binding sites
directly. They do not run record expansion to manufacture locations. Syntax-only
services can therefore describe an unsafe requested getter without claiming it
will be admitted or checked.

## Explicit lowering

[Elaboration.Declaration](../src/Fibril/Elaboration/Declaration.idr) owns record
type/constructor/eliminator/projection generation and declaration admission.
It checks erased parameter policy, parameter/field shadowing, duplicate fields,
safe projection permissions, generated-name uniqueness and expanded declaration
quotas. A cumulative generated-IR node budget is checked with a size-only
preflight before expansion; a post-generation count detects underestimated output.
Generated expressions retain their source origins.

Every generated declaration still passes through global resolution, pre-clone
core construction admission, and erased/runtime checking. The elaborator does
not install an axiom, override a field quantity, or authorize effects.
Module checking publishes exports only after all generated and ordinary
definitions are checked. Private and unused bodies remain checked.

Elaboration failures have a distinct stage and actual source position. An unsafe
getter is now an elaboration failure, not a parsing failure. Core failures remain
unlocated. Parsing a graph still reports checked: false; a graph can be
syntactically valid while its declarations fail elaboration.

Erased named globals, headerless typed-let opacity, explicit core motives,
Pi/quantity invariance, module visibility and IO planning are unchanged. Existing
structural host proofs cover the same core language; this refactor is not a new
soundness theorem.

## Inspect the expanded program

~~~sh
./build/exec/fibril elaborate examples/modules/record-projections/Data/Dictionary.fib
~~~

The command emits version-1 JSON containing:

- checked: false and representation: named-ir;not-source.
- The module/import names, without loading imports.
- Every lowered declaration, including its name, quantity, export/generated flags,
  readable signature/value IR, implementation marker, and actual source-name origin span.
- Expression IR for an expression document; pending infer-record-case nodes
  remain pending, without contextual inference or checking.

It prints the full local generated definitions rather than precomputed runtime
results. It does **not** resolve globals, typecheck the program, normalize/evaluate
it, execute IO descriptions, require main, or write files. An unresolved import
or ill-typed ordinary body can still be inspected successfully. Malformed syntax
or rejected declaration admission produces stderr/nonzero status and no success
packet.

The named IR explicitly shows Pi/lambda/Sigma/pair-case/application and
global[...] references. Internal binder names may appear. This is diagnostic
output, **not accepted source syntax**, not a serializer/round-trip promise and
not an automatic source formatter.

No compiler root is guessed. This command inspects one bounded UTF-8 file;
project checking remains the separate --source-dir path. Source spans use the
existing Unicode-scalar coordinate convention.

## API and compatibility

Explicit interfaces retain authored method signatures; elaboration owns their
automatic getter requests. Named method blocks use earlier local or checked
direct-import schemas, with ordinary constructor checking after generation. Implementations retain an explicit ordinary typed
body; checking enforces a structural dictionary target, not nominal membership
or registration. See [the implemented syntax](explicit-interfaces.md).

New compiler clients use parseDocument/parseAuthoredDeclarations followed by
elaborateDeclarations, then resolution/checking. The raw syntax/IR records are
ordinary data, not checking certificates. Elaboration rechecks parameter policy,
minimum field arity, declaration slots and generated-IR construction admission
when given manually constructed records. elaborateDeclarationsWithBudget can
lower the default 200000-node allowance; it cannot bypass the safety ceiling or
independent core/checker limits. Field/getter counts have no fixed eight-item cap.

The old parseDeclarations/parseSource compatibility entrypoints remain
ordinary-only. Their legacy ordinary-let adapter is not the project compiler
pipeline; records require the explicit authored-document/elaboration path.
DocumentBody now contains AuthoredDeclaration values. Internal clients and tests
have migrated rather than pretending the old body was already elaborated.

This refactor isolates **record declaration expansion**. It does not claim every
older expression sugar has moved out of parsing: do syntax still retains its
historical parser lowering. Contextual named-to-core processing now lives in
[Elaboration.Expression](../src/Fibril/Elaboration/Expression.idr), including
[bounded pattern motive inference](pattern-inference.md). Future changes can preserve more
surface syntax where tooling needs it.

## Next boundaries

Constructor names remain explicit; named eliminator directives are optional.
Omitting one generates no helper or fabricated source location, and consumes no
eliminator declaration slot. Automatic constructor naming,
projection defaults, inferred method argument clauses, general implicit arguments
and instance lookup need their own policy and source-origin design. They belong in elaboration,
not parser-specific function recognition.

[Source formatting](formatting.md) is separate. The initial formatter normalizes
horizontal gaps with reparsing/structure checks and no source writes. Broader
automatic formatting still needs trivia-aware rules; the named-IR printer is not
a shortcut for rewriting source files.
