# Design: nominal interfaces

Status: proposal, not implemented. Nothing here has been prototyped; claims about existing
code were read from source, and open checks are listed at the end.

## Problem

An `interface` lowers to a transparent record alias whose body is a `Sigma`/`Box` of its method
types ([records](records.md), `recordDeclarations` in `Elaboration/Declaration.idr`). `Add Word`
and `Sub Word` with the same method shape therefore normalize to one term. Everything that
compares dictionary types sees them as the same type:

- `Add` and `Sub` over one type cannot both be inferred ([constraints](constraints.md#inferred-dictionaries-after-implicit-arguments)),
  so `+`, `-` and `*` cannot each have an interface of their own ([operators](operators.md)).
- A plain record, or a dictionary of the wrong interface, is accepted wherever a same-shaped
  interface is expected ([constraints](constraints.md), "structural dictionary typing").
- `@{implementation}` lookup, local `@{}` selection and inferred insertion all pick by type, so
  they inherit both problems.

## Goals and non-goals

Goals: two interfaces are different types even when their methods have equal types; `Add Word`
and `Add String` stay different as now; no new kernel rule; existing `interface`,
`implementation`, `@{...}` and `=>` source keeps working.

Non-goals: records stay structural (unchanged, see [nominal data](nominal-data.md)); no
superclasses, no recursive instance search, no coherence theorem, no law checking.

## Options

**A. Lower an interface to a one-constructor nominal `data` type (recommended).** The kernel
already has `NominalType key params shape` with exact-key identity, built for `data` by
`buildData`. An interface becomes a single-constructor type whose fields are the methods. The
constructor, eliminator and case form already exist for data, and `NominalType` compares the key
first, so `Ops.Add` and `Ops.Sub` differ with no new rule.

**B. Tag providers and constraints with an interface name (metadata only).** Inferred lookup
would filter by name. Rejected: type checking would remain structural, so an `Add` dictionary
could still be passed where `Sub` is expected, and local dictionaries have no recorded name.

**C. Add an erased tag field to every dictionary.** Works, but is a hack on top of the structural
record and needs a hidden tag type per interface. Option A is the same idea done properly.

**D. Make every record nominal.** Larger, and a deliberate decision in `nominal-data.md` was not
to change record identity.

## Proposed design (option A)

For `interface Add (0 A : Type 0) : Type 0 where` with methods `m1 ... mk`:

1. **Type.** A global `Add` whose body is `NominalType "<Module>.Add" [A] (VariantType [one arm])`.
   The arm's payload is the method record (as today), so the shape is unchanged inside the wrapper.
   The key is the module-qualified declaration name, as for data, so it is stable across imports and
   facades.
2. **Constructor.** `MkAdd` builds the nominal value, as a data constructor does.
3. **Getters.** Each method getter becomes an ordinary function: unwrap the nominal value, then
   project the field. It still consumes its dictionary once and takes the interface parameters
   first, so call sites do not change.
4. **Eliminator.** The optional `eliminator` keeps its type, generated the way data eliminators are.
5. **Dictionary-shape gates** accept a `NominalType` whose shape is one arm holding a record, in
   addition to `Box`/`Sigma`: `dictionaryTypeGlobals` and `candidatesGlobals`
   (`Elaboration/Expression/Dictionary.idr`) and `dictionarySignatureGlobals` (`Driver/ModuleCheck.idr`).
6. **Implementation blocks** call the constructor, so `InterfaceSchema` stays as it is.
7. **Selection** needs no change: candidate comparison is bounded conversion of the required type,
   which now includes the key.

Everything is built from existing core terms and independently rechecked by the core checker.
No term, conversion rule or runtime support is added.

## What changes for users

- Source that declares and uses interfaces is unchanged.
- Behavior that relied on structure stops working, deliberately: passing a record or another
  interface's dictionary as an interface dictionary is now a type error, and `docs/constraints.md`
  ("a same-shaped record can match") and `docs/explicit-interfaces.md` ("structural dictionary
  type") must be rewritten.
- Two interfaces with equal method types, in any modules, are distinct types, so `Add`, `Sub`
  and `Mul` can each be an interface.
- `elaborate` output for interfaces changes.

## Edge cases to settle

- **Quantities.** Methods are unrestricted fields; the wrapper must not make the payload linear in a
  way that stops a reusable (unrestricted) dictionary from serving many calls.
- **Facades and re-exports.** `InterfaceSchema.constructorOrigin` already tracks the checked origin;
  the key must use that origin, not the visible name.
- **Parameters.** The record limit of 8 parameters and any data-field limit should agree, or the
  stricter one must be documented.
- **Dependent methods** (a later method type mentioning an earlier method) must still lower.
- **Cost.** The shape is compared as well as the key. Compare keys first and skip the shape when equal
  if the kernel allows it; otherwise measure dictionary-heavy examples against the existing
  admission counters.
- **Factories** (functions returning dictionaries) return the nominal type; check the "factory
  returns a dictionary" test in `dictionarySignatureGlobals`.

## Plan

1. Prototype the lowering for one interface by hand in a test module; confirm it checks and that
   `Add Word` and `Sub Word` become distinct.
2. Switch `lowerItem (InterfaceItem ...)` to emit the nominal declaration set; update the three gates.
3. Update docs and the structural-matching tests; add tests for: distinct same-shaped interfaces,
   wrong-interface dictionary rejected, record no longer accepted, export/import and facade keys,
   reuse of an unrestricted dictionary, `+ - *` each with its own interface.
4. Revisit `examples/modules/operators` to give `-` and `*` interfaces.

## Open checks before implementing

- Does one-constructor data accept an unbounded method count, and unrestricted named fields, through
  the *source* `data` path, or only through core `buildData`? Records have no field cap; data may.
- Can `eliminator` and `case` over a nominal single-arm payload be generated at the `Expr` level
  (`NNominalType`, `NNominalValue`, `NNominalCase`, `NVariant*` exist), or must interfaces use the
  driver's `DataFamilies` route?
- Which existing tests assert structural interface behavior? `grep` finds the one at
  `tools/test_cli.py:4084` and the docs above; a full run will find the rest.
