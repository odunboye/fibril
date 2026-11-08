# Shared checked globals

Named module declarations now use environment-local `GlobalRef` keys instead of
embedding their signatures and bodies at each reference site. This applies to
module/package checking, hosted evaluation and console/binary execution, and
native console/binary emission. Plain expression/local-binder syntax keeps its
existing APIs. Bootstrap primitive/prelude definitions retain their compatible
expanded representation.

## Admission and trust

`Core.Erased.GlobalContext` and `Core.Runtime.RuntimeGlobals` have private
constructors. Environments grow monotonically. A declaration's signature must be
a type, its body must check against that signature, and it may refer only to
previously admitted keys. Duplicate identities, forward/self references and
linear global ownership are rejected. Non-erased bodies additionally pass the
ordinary runtime usage checker. Erased admission alone cannot authorize runtime
execution.

A source `GlobalDefinition` remains raw resolver metadata. Its optional shared
key is not a certificate: a raw `GlobalRef` has no embedded type or body, and the
core rejects a key absent from the supplied checked environment. Qualified,
short, selective and public-import aliases preserve the same key. The source
visibility inventory still controls which names can be resolved; access to the
checking environment does not grant access to private source names.

Keys are local to one checking session. They are not package identities, stable
serialization identifiers, or a cross-project cache contract. Moving a raw term
to a different environment changes the interpretation of its keys and requires
checking it again.

The reference typing rule reads only an admitted signature:

```text
Delta[g] = (quantity, A, body)
----------------------------------
Delta ; Gamma |- GlobalRef g : lift(A)
```

Here `A` and `body` are closed in computational variables and use only earlier
keys. The environment builder establishes formation and checking before adding
`g`; `lift` changes the local variable scope without changing any global key.
Runtime analysis assigns zero local usage to an unrestricted reference and
rejects an erased reference in a runtime position. This is an implementation
contract, not a metatheoretic soundness or erasure-preservation proof.

## Conversion and runtime behavior

Signatures are read from the checked environment. Bodies unfold transparently
when conversion or evaluation needs them. Each unfolding spends an ordinary
reduction unit; exhaustion remains distinct from rejection and never discharges
a type obligation. Term renaming and substitution preserve global keys without
entering their bodies. The existing binding laws include the new constant case.

Runtime usage checking rejects an erased global before evaluation can erase or
normalize away its occurrence. References passed to erased arguments remain
available for erased checking. A closed earlier global cannot contain the local
self variable of a later `Fix`; termination extraction treats that reference as
closed and does not infer a decrease from a global-headed result. A separate
walk checks each referenced signature/body against the extractor's existing
supported-syntax boundary, so a reference cannot conceal an unsupported form.

Native emission writes one body per reachable declaration, with reference
functions entering that body through `f_global`. This enters the existing
runtime evaluation/depth budget with an empty local environment. It does not
introduce a process-wide value cache: separate uses may recompute a global.
Laziness, quantities, effect staging and the existing runtime limits remain in
force.

## Whole-graph admission

A reference is one node of syntax. The module construction estimate charges
signature/body construction at declaration admission rather than at each use.
The existing 200000-unit construction budget remains an admission policy, not a
CPU/heap bound.

[Construction accounting](construction-accounting.md) now releases a named
declaration's unused preflight reservation after checking its emitted size.
Committed signature/body nodes remain cumulatively charged across modules.

Native and hosted-binary admission use an explicit **reachable graph policy**:
count the complete entry plus every reachable signature and body once. Aliases
and repeated references do not duplicate that charge. The numeric native/binary
limits remain 8192 nodes and 8192 literal/key characters. This changes the unit
from an expanded tree to stored shared syntax; it is not evidence that earlier
expanded-tree experiments fitted their old gates.

Reachability includes references in types, annotations, erased arguments and
unselected branches. Capability scans inspect the complete syntax of each such
declaration before any execution or emission. Masking a reference for these
scans is allowed only after collecting its definition; masked syntax is never
used for checking, conversion or execution. Legacy scans conservatively reject
unresolved references.

The source file, graph, package, parser, evaluator and runtime limits remain
separate. An unreferenced private declaration is still checked, although its
unused effects do not become capabilities of the entry. Source errors still
prevent all execution.

## Regression workloads

`Tests.SharedGlobals` covers environment admission, rejected forgeries and
cycles, erased barriers, local binding transport, fuel exhaustion, and a
64-level chain that references each predecessor twice. Its stored graph is
linear in the number of declarations; eager expansion would be exponential.

`tools/test_shared_globals.py` checks source-level repetition through hosted
execution and compiled C, canonical imported aliases, erased aliases, invalid
private bodies, hidden binary effects, reachable literal admission and the
larger email model. It is part of `make test`. Run it with sanitizer flags in
`CC` to exercise the generated C/runtime boundary.

`test/fixtures/modules/email-service-full` retains an eight-status/eight-event
compiler regression model; the application now lives separately in `../email`.
It includes deferral/retry, failure, delivery, bounce and uncertain submission.
Its hosted/native demonstration is still a pure state model: it performs no
network, storage, authentication or real mail delivery.

## Remaining limits

This is shared program representation, not an incremental compiler, a linker,
a memoizing evaluator or an ownership proof. Lookup and environment construction
currently use lists; large inventories can still have quadratic overhead.
Transparent normalization can still repeat work and produce large terms within
its fuel policy. There is no total CPU/heap bound or semantics-preservation
proof. The bootstrap prelude can be migrated separately. Historical parser/LSP
measurements must be rerun before claiming a throughput improvement.

The [composed workload probe](composed-workloads.md) measures the current graph
policy separately from those historical expanded-tree records.

Current hosted diagnostic observers pass the checked environment and report
reachable shared-graph size, so a one-node entry reference cannot hide its
program's footprint. The older tree-schema cost auditor uses a separately tagged,
budgeted expansion compatibility view (200000 construction units, depth 128).
That view is an offline observer only; it does not change compiler admission or
execution. Retained historical JSON evidence is not rewritten or presented as a
measurement of this implementation.

The legacy cost/admission probe refuses this compatibility view rather than
comparing expanded-tree counts against the new shared-graph admission rule.
Its admission-evidence schema must be migrated before collecting new cost rows.
The raw NatCase/WithRegion observer regressions remain usable.
