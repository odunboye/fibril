# Guarantees and non-guarantees

Status: **the policy below is the target. Only the rows marked implemented or
partial in the status table are enforced today, and none of them is a soundness
proof.** The checker is experimental: `check --json` reports `accepted` as the
runtime checker's decision, "not a soundness proof".

- Total by default; explicit partial computation must not establish trusted proofs.
- Quantities 0, 1, and unrestricted are checked statically under rules still to be specified.
- Erasure must preserve observable computation, including relevant transport.
- Axioms, runtime unsafety, and foreign assumptions must remain visible and distinct.
- Foundations are selected project-wide; switching requires rechecking.
- C and JavaScript must preserve specified shared semantics.
- Bare-metal support does not imply bounded timing.
- Hard-real-time claims require target/application-specific evidence.
- Termination, linearity, self-hosting, and kernel size alone do not establish
  consistency, compiler correctness, bounded memory, or deadline guarantees.

## Status of each policy

| Policy | Status | What exists, and what does not |
| --- | --- | --- |
| Total by default | **Implemented for the compiler; enforced by test** | Every `src/Fibril` module declares `%default total`. The checking kernel (`Core`, `Elaboration`, `Termination`, `Foundation`, `Cubical`, `Source`, `Data`, `Effect`) contains no `partial`/`covering` declaration and no `assert_total`, `believe_me` or similar. [test_trust_inventory.py](../tools/test_trust_inventory.py) fails CI on any new escape and pins the existing ones: `covering` in eight hosted-IO and entry-point files, and two justified `assert_total` calls in the C backend. Recursion in Fibril source is accepted only when structural or admitted by a size-change check. This says nothing about the *correctness* of the checker. |
| Quantities 0 / 1 / ω | **Partial** | The runtime-usage checker enforces binder quantities in `check` ([erased-checker](erased-checker.md), [runtime-checker](runtime-checker.md)). The rules are documented as prototype scope, not as a specification, and there is no soundness theorem. |
| Erasure preserves computation | **Prototype, not established** | An erased checker exists and is documented as "not the complete Fibril kernel". No erasure-preservation theorem is claimed. Cubical admission proves erasure equalities only for its narrow `refl` subset. |
| Axioms / unsafe / foreign assumptions visible | **Nothing to show yet** | The language has no axiom, `unsafe` or foreign-declaration form, so none can be introduced; source comments state that the Prelude and globals are checked, "not axioms". There is therefore no trust report either. A foreign-function boundary needs its own design first. |
| Foundations project-wide | **Partial** | Manifests carry a required `foundation` field and only `de-morgan` is admitted. `fibril.lock` records it, so a change shows as lock drift. No second foundation exists, so "switching requires rechecking" is untested. |
| C and JavaScript share semantics | **Experimental subsets; differential tests** | Emitted C supports checked console/binary IO, pure data, bytes and `Word`. [JavaScript](javascript.md) supports output-only ES modules with exact `BigInt` Words and shared data lowering. Tests compare successful programs in the common fragment with hosted evaluation and C; this is not a general semantic-preservation theorem. Input, binary transport, regions, HTTP, storage, UI and FFI are outside the JavaScript fragment. See [native-c](native-c.md). |
| Bare-metal; hard real time | **Portable no-heap C subset; no real-time guarantee** | The [C arena profile](embedded.md) uses caller-owned typed storage and explicit output callbacks; its generated/runtime objects have no heap allocator or stdio references. There is no firmware/MCU port or measured stack/WCET guarantee. Callbacks, target support routines and startup code remain the host’s responsibility. |

Cubical term checking is **not** part of the trusted core. A narrow guard checks
`cubical NAME : L = R by refl` between closed, independently elaborated pure
definitions during ordinary `check`; it does not change production conversion
([cubical-source](cubical-source.md)).

Rows marked partial, prototype, none or not implemented are **not** guarantees.
Even "implemented" describes enforcement in this compiler, not a proof that the
checker is sound.

The experimental [TCP profile](network.md) adds opaque stream/listener types and
ownership-returning socket operations, with a trusted POSIX boundary and bounded
Fibril exact reads. It does not provide TLS, DNS, an asynchronous scheduler, HTTP
or a database driver. Effects are incremental and can leave a visible prefix.
