# Checked non-recursive declaration construction

## Use cases

**Implemented internal API D2b, alongside [non-recursive source data](data.md).**
This closed-core API complements the named-IR source elaborator: provide scoped erased parameters,
variant alternatives and constructor names, and obtain ordinary independently
checked definitions plus layout metadata. A parser must not manufacture trusted
constructors just because a name/schema says they exist.

For compiler development, an Optional A specification generates a checking-only
type family and ordinary Nothing/Just functions. A Result-like specification can
choose among multiple payloads; a dependent record/Sigma can serve as one payload
package with many fields. This API does not yet parse or pack source constructor
field telescopes. Prefer existing source records/functions for current .fib
programs; DataSpec itself is not source syntax. Source data now supports curried
constructor field telescopes through named IR; both routes share nominal/variant
kernel checks and qualified key allocation.

![Checked declaration bundle](diagrams/data-declarations.svg)

## Input and output

[Elaboration.Data](../src/Fibril/Elaboration/Data.idr) provides an untrusted
DataSpec n with:

- Identifier components for a named module and type.
- A declared literal universe level.
- A scoped Context n of erased parameters.
- A nonempty list of nullary/payload variant descriptors in that scope.
- Exactly one referenceable constructor name per alternative.

This is a host Idris example, not Fibril source:

~~~idris
optional : DataSpec 1
optional = DataInput ["Example"] "Optional" 0
  (Extend Empty Erased (Universe 0))
  [Nothing, Just (Linear, Variable FZ)] ["Nothing", "Just"]
~~~

buildData 200000 [] optional returns a bundle whose type key is Example.Optional
and whose constructors are Example.Nothing and Example.Just. Applying the latter
to String and "present" constructs a checked value at Example.Optional String.
Constructor definitions have ordinary Pi/Lambda types/values and can be rechecked
without a special declaration-acceptance rule.

The bundle includes an erased type global, unrestricted constructor globals,
layout tags/quantities, and a remaining node budget. No result is installed in a
global environment, registered as an instance or executed. A failed check returns
only an error, not partial constructor/layout output.

## Canonical names and non-recursion

Keys join validated module/type identifier components with dots. Constructors
use module-qualified names, as other module bindings do. Components must be
single referenceable non-keyword identifiers, not dotted paths, whitespace or
wildcards. Type/constructor collisions and caller-supplied occupied qualified
bindings are rejected. Qualified names are unambiguous because components cannot
contain dots. File containment, module component/profile limits and direct-import
authority remain driver responsibilities.

The complete parameter vector is retained in NominalType, including phantom
parameters. Its variant shape is independently checked. A key is not a typing
certificate, and this API cannot make two inconsistent shapes interchangeable.

Explicit occurrences of the declaration's own nominal key in parameter domains
or payloads are rejected by structural traversal, including through application,
annotations, indices, binders and nested shapes. A string literal containing the
same text is not a type reference. This conservative rule also rejects a self
occurrence in a beta-discarded argument; it is not a positivity checker or general
alias/recursive-declaration resolver. Recursive references are not installed.

## Checking and staging

The builder closes scoped parameters with ordinary erased Pi/Lambda binders.
It checks the type-family value against its declared signature through the
ordinary erased checker, and every constructor through the ordinary runtime
checker. Malformed context domains, payload kinds, permissions and universe
claims therefore cannot enter through metadata.

The family body receives an explicit universe ascription before its parameters
are closed. Literal universe upward compatibility does not propagate through Pi
conversion; the ascription preserves a higher declared family universe without
changing that invariant. Constructor result annotations use the same declared-
signature-preserving global occurrence as ordinary source resolution.

Type globals are erased. Constructor globals are unrestricted but their payload
argument permissions remain exact. They are not dictionary implementation
providers. An erased global occurrence remains forbidden as a runtime value;
types/indices do not become runtime evidence by being retained in a signature.

## Admission before construction

The caller supplies a cumulative core-node budget and occupied qualified names.
A size-only preflight counts all repeated parameter domains, phantom index cells,
shape annotations, global ascriptions and constructor applications **before**
generated definitions are constructed. Each actual generated definition is then
counted; the observed total must equal the estimate exactly. The returned
remainder lets later bundles share the same budget.

[Core.Size](../src/Fibril/Core/Size.idr) now owns the structural counter also used
by module admission, plus explicit nominal-key traversal. Existing source-work,
checker depth and reduction policies still apply. There is no fixed alternative
count cap; payload packages can use existing resource-budgeted records. The core
node budget is not a bound on raw host input text, checking allocation or time.
Source/file/name-profile admission belongs to the future frontend integration.

## Metadata and remaining gates

DataBundle/DataLayout are ordinary public data, not proof objects. A forged
record is not a checked declaration. Future consumers must validate constructor
references against checked signatures and canonical packing, and the module
driver must publish metadata only after all declarations in a dependency check.
This function's all-or-error return does not itself implement module publication.

[Tests.DataDeclaration](../test/src/Tests/DataDeclaration.idr) covers generated
constructor rechecking/instantiation, qualified names, phantom distinctions,
levels/staging, name/count/permission/kind failures, structural self detection,
multiple alternatives, dependent packages, exact preflight and cumulative budget
exhaustion. Kernel tests and core structural proofs remain distinct from whole-
language preservation, positivity, normalization or verified erasure evidence.

[Authored data grammar](data.md), source field-telescope packing and ordinary
checked module exports now work through named IR. Next: exhaustive flat constructor
matching with direct branch resource joins. Recursive
inductives, strict positivity, termination and cubical data remain separate work.
