# Design: nominal interfaces

Status: proposal, revised after a review and a hand prototype. Nothing is implemented in the
compiler. The "Evidence" section lists what was run; everything else is reasoning from source.

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
already has `NominalType key params shape`, built for `data`. An interface becomes a
single-constructor type whose fields are the methods. Types with different keys never convert, so
`Ops.Add` and `Ops.Sub` differ with no new rule.

**B. Tag providers and constraints with an interface name (metadata only).** Rejected: type
checking would remain structural, so an `Add` dictionary could still be passed where `Sub` is
expected, and local dictionaries have no recorded name.

**C. Add an erased tag field to every dictionary.** Works, but is the same idea as A done as a hack
on top of the structural record.

**D. Make every record nominal.** Larger, and `nominal-data.md` deliberately left record identity
alone.

## Proposed design (option A)

For `interface Add (0 A : Type 0) : Type 0 where` with constructor `MkAdd` and methods `m1 ... mk`:

1. **Lowering.** `lowerItem (InterfaceItem r)` builds a synthetic `DataDeclaration` from the
   `RecordDeclaration` and calls the existing `lowerData`. The fields map one to one:

   | RecordDeclaration | DataDeclaration |
   | --- | --- |
   | `name`, `level`, `params`, `exported`, `span` | same |
   | `constructorName`, `fields` | one `DataConstructor` with `result` = the type applied to its parameters |
   | `eliminator` | `eliminator`, or a private generated name when none was requested |
   | (none) | `implicitConstructors = False`, `indices = []` |

   The type, constructor and key are then produced by the same code as ordinary data, so identity
   is the module-qualified declaration name.
2. **Getters.** Each method gets an ordinary function that applies the generated eliminator with the
   method's type as its motive, selecting field *i*:
   `get_i P1..Pn d = elim P1..Pn (\self => T_i) d (\m1 ... mk => m_i)`.
   It consumes its dictionary once and takes the interface parameters first, as today, so call sites
   do not change. **Do not use a direct `case` here:** it stops working between 8 and 12 fields
   (see Evidence).
3. **Dictionary-shape gates** accept a `NominalType` whose shape is a single arm, in addition to
   `Box`/`Sigma`, at: `dictionaryTypeGlobals` and `candidatesGlobals`
   (`Elaboration/Expression/Dictionary.idr`) and `dictionarySignatureGlobals` (`Driver/ModuleCheck.idr`).
   Without this, constraint binders and `implementation` items reject the new types (shown below).
4. **Implementation blocks** call the constructor, so `InterfaceSchema` and `lowerImplementation`
   stay as they are.
5. **Selection** needs no change: candidate comparison is bounded conversion of the required type,
   which now includes the key.

Everything is built from existing core terms and independently rechecked. No term, conversion rule
or runtime support is added.

## Evidence (hand prototype on current master, `fibril` built from this branch)

Interfaces were written by hand as one-constructor `data` and exercised.

| Check | Result |
| --- | --- |
| `Sub Word` value where `Add Word` is expected | rejected, `$global3 @ Word` vs `$global0 @ Word` |
| getter by `case d of MkAdd method => method l r` | works, evaluates to 42 |
| two-method getter by direct `case` and by eliminator | both work |
| direct `case` over *n* fields | ok for 2, 3, 4, 5, 6, 8; **fails at 12, 16, 24** ("Constructor does not expose the requested fields") |
| eliminator getter over *n* fields | ok for 2 through 24 |
| one unrestricted dictionary used twice | works (`twice 5w` = 15) |
| linear method arguments `(1 l : A) -> (1 r : A) -> A` | works |
| polymorphic method `(0 B : Type 0) -> B -> B` | needs `: Type 1`, as it does for interfaces today |
| 12 methods in one constructor | works |
| `=>` constraint binder over the nominal type | **rejected**: "requires a dictionary-shaped unary or dependent-pair type" |
| `implementation` over a plain data type | rejected (also expected: not an interface) |
| hosted `run` and `emit-c` of a case-based getter with a function field | both print the right output |
| width, all getters generated | nominal ok at 16 and 20 methods; **today's interface fails at 16** ("Generated declaration construction budget exhausted") |

So the nominal form is *wider and no slower* than the current lowering, and the two gates in item 3
are the only places that must change for selection to work.

## What changes for users

- Source that declares and uses interfaces is unchanged.
- Behavior that relied on structure stops working, deliberately: passing a record or another
  interface's dictionary as an interface dictionary is a type error. `docs/constraints.md` ("a
  same-shaped record can match") and `docs/explicit-interfaces.md` ("structural dictionary type")
  must be rewritten, and the assertion near `tools/test_cli.py:4084` changes.
- Two interfaces with equal method types, in any modules, are distinct types, so `Add`, `Sub` and
  `Mul` can each be an interface.
- The optional `eliminator` helper's type changes slightly: a record eliminator takes its branch
  with quantity 1, a data eliminator takes it unrestricted. No example, test or doc in the repo
  calls an interface eliminator, so the risk is low. Either accept the data form or hand-write the
  linear-branch form.
- `elaborate` output for interfaces changes shape.
- A single-constructor `data` type also becomes acceptable as a dictionary type, because the gate
  looks at shape. Providers are still only values declared with `implementation`, so nothing is
  selected implicitly that was not before. Restricting the gate to interface keys is possible but
  needs a registry; it is not proposed.

## Corrections to the first draft

- "`NominalType` compares the key first" was wrong. Conversion normalizes the indices and the shape
  and compares all three (`stepWithGlobals` in `Core/Reduction.idr`); there is no key shortcut. The
  shape was already compared structurally before, so cost is unchanged.
- Getters by unwrapping and `case` do not scale; use the eliminator.
- The open question about field limits is answered: `docs/data.md` states there is no fixed
  constructor or field count cap for data, and the nominal form passed at widths where today's
  interface fails.

## Remaining risks and checks

- **Dependent methods** (a later method type mentioning an earlier method) make a getter's motive
  mention a variable that is not in scope outside the branch. Check what `projectionDeclaration`
  does for records today and match it.
- **Facades and re-exports.** Verify the key comes from the defining module for a re-exported
  interface and that `InterfaceSchema.constructorOrigin` still lines up.
- **Zero-parameter interfaces** exist in examples (`interface Append : Type 0`); confirm they lower.
- **Error messages and tests.** `tools/test_cli.py` mentions interfaces about 60 times; a full run
  will show which assertions depend on the old shape.
- **Native backend** was checked only for a hand-written dictionary with a case getter; run the
  existing interface examples natively after the switch.

## Plan

1. Add the gate change and a synthetic-lowering function; keep the old path behind the same entry
   point until the suite passes.
2. Generate getters through the eliminator; add tests for distinct same-shaped interfaces,
   wrong-interface and record rejection, unrestricted reuse, export/import and facade keys, and
   widths up to 20.
3. Update the docs listed above and the structural-matching test.
4. Give `-` and `*` interfaces in `examples/modules/operators`.
