# General recursive data: plan

The non-indexed admission rule below is the foundation. The implemented extension
for separate erased indices and index-aware dependent cases is documented in
[indexed inductive families](indexed-data.md); indexed families are no longer
globally unsupported. Nested and mutually recursive data remain outside both slices.

**Status: phases 1 to 4 and the first slice of phase 5 are implemented (core terms, reduction,
declaration admission, typing, termination, run-mode evaluation, and source `data` and `case`
for general families, and native emission); function equations with constructor patterns
are not.** It records what restricts recursive
data today, what the smallest sound extension is, and the phases to land it. It is not a
positivity theorem or a soundness claim.

## Use cases

Fibril can declare only two recursive shapes (`Chain`-style unary, `Items A`-style list),
each a separate family of core terms. Programs cannot write:

- a binary or n-ary tree (`Node : Tree -> Tree -> Tree`);
- a list whose elements may be dropped (an unrestricted head);
- a recursive type with extra payload fields, several constructors, or unrestricted
  recursive fields (a copyable `Tree`);
- an expression language (`Add : Expr -> Expr -> Expr`, `Lit : Nat -> Expr`).

Without these, real programs cannot be written even after general recursion landed. The
probe that shows it: `Node : (1 left : Tree) -> (1 right : Tree) -> Tree` fails with
"Recursive data or type-name shadowing is not supported".

## Why today's design cannot just be widened

Each fixed shape is its own set of core terms (`RecType/RecEnd/RecMore/RecFold/RecCase`,
`SeqType/SeqNil/SeqCons/SeqFold/SeqCase`). Each is threaded through about 25 files
(renaming, substitution, reduction, weak head, erasure and runtime checking, size, pretty
printing, evaluation, termination extraction, native emission). Positivity holds "by
construction" because the shape is hard-wired. Adding a third and fourth hard-wired shape
would repeat that cost per shape and never reach general data.

## Proposed design

One general family, checked against a declaration, instead of one term set per shape.

### Core terms

| Term | Meaning |
|---|---|
| `DataType key params` | the type `key` applied to its parameters |
| `DataCon key index params fields` | constructor `index` with its field values |
| `DataCase motive scrutinee branches` | one-layer, dependent, exhaustive elimination |

There is **no general fold term**. Recursion goes through `Fix`, which already exists and
is gated by size-change termination. The only new termination fact needed is that a field
bound by a `DataCase` branch on a scrutinee is **strictly smaller** than that scrutinee,
for fields whose declared type is the recursive family. The extractor already tracks this
relation for `NatCase`, `SeqCase` and `RecCase`; it gains one more case.

### Declaration environment

A checked `DataDecl` is registered once under its qualified key:

```
DataDecl { key, parameters : telescope (erased, Type 0)
         , constructors : List (name, fields : telescope of (quantity, type)) }
```

The checker looks declarations up by key, the way shared checked globals are looked up
(`GlobalRef`). Terms stay small: constructors carry the key and index, not the signature.

### Positivity (the soundness-critical rule)

Start deliberately narrow, so the rule is simple enough to argue by hand:

1. A recursive occurrence `key params` may appear **only as the entire type of a field**.
   Not under a function arrow, not as an argument to another type former, not in an index.
2. Parameters are the same in every recursive occurrence (uniform).
3. Field types may mention earlier fields only through ordinary dependency, never the
   family itself.

Everything the fixed shapes accept is a special case. Nested, mutual and indexed families
stay out of scope, as they are today.

### Quantities

A field has its own quantity. The existing rule is kept: extracting a **linear** field from
an **unrestricted** scrutinee is refused, since it would duplicate a linear resource. What
changes is that a family may now declare **unrestricted** recursive fields, which makes the
whole value copyable. `len : (t : Tree) -> Nat` then works with an unrestricted parameter,
which is exactly what the earlier probe showed was impossible. Linear recursive fields keep
working for resource-carrying data.

### As implemented in phases 1 and 2

- `DataCon key index leading` records how many leading arguments are parameters, so
  `DataCase` reduction picks branch `index` and applies it to the remaining arguments
  without consulting the declaration. Branch lookup that fails leaves the case stuck.
- Until phase 3, `infer`/`analyze` refuse all three terms, the termination extractor
  rejects them as an unsupported form, and the C emitter rejects them. Nothing can
  construct or consume general data by accident.
- `admitDeclaration` takes a `DataDecl` (a `Telescope` of erased parameters and a
  telescope of quantified fields per constructor, each field in the scope of the
  parameters and earlier fields). A field type that mentions the family must be exactly
  the family applied to the parameter variables in order. A mention anywhere else, under
  a function type, in a parameter type, or inside another former, is refused with the
  constructor and field position.
- Parameters must be erased; constructor names must be non-empty and distinct.

### As implemented in phase 3

- The declaration table is a second field of `GlobalContext` (`dataDeclaration`), so a
  family lives beside the checked globals and shares their immutability. Moving it into
  the shared-globals environment later only changes where the lookup reads.
- `formerType decl` is `(0 p1 : P1) -> ... -> Type 0`; `constructorType decl i` is the
  parameters (erased), then the fields with their declared quantities, ending in the family
  applied to the same parameters. `DataType`/`DataCon` simply have those types, so ordinary
  application checks constructor arguments and charges their quantities.
- `DataCase` needs a scrutinee whose type is the family applied to parameters, an erased
  motive over that type returning a universe, and exactly one branch per constructor. The
  expected branch type is the constructor type with the actual parameters instantiated and
  its result replaced by the motive applied to the constructor rebuilt from the fields.
- `extendDataGlobals` runs `admitDeclaration`, requires a fresh key, checks every
  constructor type with the family already in scope (safe, because positivity allows the
  family only as a whole field type), and requires field types in Type 0. A field in a
  larger universe is refused: the family is declared in Type 0, so allowing it would make
  the family impredicative.
- Runtime usage: the family former is a type expression, a constructor constant costs
  nothing (its arguments are charged by the application through the Pi quantities), and a
  case adds the scrutinee's usage to the joined usage of its branches, like `VariantCase`.
  A linear field must therefore be consumed in its branch.
- Not done: termination (phase 4), source syntax (phase 5), native emission (phase 6).
  The termination extractor and the C emitter still reject the new terms.

### As implemented in phase 4

- `Extract.extractFixWith` takes a `FieldCounts` function (`family key -> constructor index ->
  number of fields`). The extractor cannot see declarations, so `Erased` supplies one from the
  global context (`fieldCountsOf`). Without it a case on a family is unsupported, so the
  older entry points (`extractFix`, `admitFix`) still fail closed on general data.
- The count matters for soundness: a branch is a lambda over the fields, and a branch that
  returns a function has further lambdas. Peeling exactly `count` lambdas keeps the extra
  ones from being mistaken for fields (and a call under them is refused anyway).
- A field is credited as smaller only if its binder annotation is the family itself (any
  parameters). That is the same restriction as the fixed shapes, which credit only the
  tail. Every proper component of a finite value is smaller, so crediting more fields
  would also be sound; it is left for a later slice.
- The extractor takes the count function as an ordinary argument. A first attempt used an
  auto-implicit argument; Idris proof search then silently supplied `\_ _ => Nothing` instead
  of the parameter in scope, which made every case look unsupported. Do not reintroduce it.
- Evaluation needed no change beyond phase 1: `unfoldOne` already reaches case scrutinees
  and constructor arguments.

### As implemented in phase 5 (first slice)

- No new surface syntax. `lowerData` routes a recursive declaration that is neither fixed shape
  (`generalRecursive`) to `lowerGeneralData`, and `lowerModule` puts a `DataFamily` item before
  the ordinary declarations. Those declarations give the family name the value
  `\params => DataType key params` and each constructor the value `DataCon key index leading`,
  with the authored signature as its type.
- `registerFamily` (in `ModuleCheck`) elaborates the parameters, then each constructor's
  fields in the parameters' scope, with the family's own name visible as a provisional
  declaration (`withProvisionalFamily`), normalizes the field types so the recursive occurrence
  is syntactically the family, and calls `extendDataRuntimeGlobals`. The scope after the
  parameters has a runtime width, matched to the telescope length with `decEq`.
- `case` on a family (`elaborateFamilyDataCaseGlobals`) resolves each arm's constructor from
  its global's value, peels the instantiated constructor type to bind the fields with their
  quantities, and uses a constant motive built from the expected type. `NDataType` and
  `NDataCon` are the two new named-IR nodes.
- The termination check needed no further change: a function over a family that matches with
  `case` and recurses on a family-typed field goes through the existing general-recursion
  fallback and the phase 4 extractor.

### As implemented in phase 6

- `Emit.idr` lowers `DataCon` to a lambda chain over its parameters and fields ending in a
  `VariantValue` (tag = constructor index; payload = nothing, the field, or the fields as
  right-nested `PairValue`s), and `DataCase` to a `VariantCase` whose multi-field branches are
  wrapped to unpack the pair nest. The pair annotation carries each field's quantity so erased
  fields stay erased. `DataType` is an erased constant.
- Lowering calls `generate` on the term it builds, wrapped in `assert_total`: the built term
  contains only lambdas, pairs and variants, so it never reaches the lowered forms again.
- Verified against the hosted evaluator for the shipped example and for a family with
  zero-, one-, two- and four-field constructors. Native budgets are unchanged.

### What does not change

Conversion treats `DataCon` as a constructor and `DataCase` on a constructor as reducible,
like `NatCase`. `Fix` stays neutral in conversion. The existing `Chain` and `Items` shapes
keep their terms during migration; moving them onto the general family is optional and
last.

## Phases

| Phase | Deliverable | Must not claim |
|---|---|---|
| 0 | This contract, plus a list of the touch points per core module | any implementation |
| 1 | **Done.** `DataType/DataCon/DataCase` in `Term` with renaming, substitution (and their proofs), size, pretty, syntax equality, global traversal, reduction and weak-head contraction | typing |
| 2 | **Done.** `Fibril.Core.DataDecl`: telescopes, `DataDecl`, and `admitDeclaration` (positivity plus caps of 4 parameters, 16 constructors, 8 fields) | soundness proof |
| 3 | **Done.** Typing in `Erased` and `Runtime`: closed constructor types derived from the declaration, dependent erased motive, exhaustive branches with field quantities, usage joins; `extendDataGlobals` / `extendDataRuntimeGlobals` register a family | termination |
| 4 | **Done.** `Extract.idr` credits family-typed fields of a `DataCase` branch as smaller than the scrutinee; `Fix` over a family is admitted by the size-change gate; run-mode evaluation unfolds through the case | native support |
| 5 | **First slice done.** Source `data` declarations beyond the fixed shapes, constructors as ordinary functions, `case` with an expected type; **not yet** pattern equations | pattern-clause groups |
| 6 | **Done.** Native emission by lowering in `Emit.idr` to existing variants and pairs; no new C runtime code | scale |
| 7 | Optional: migrate `Chain`/`Items` onto the family; docs, examples (tree, expression language) | |

## Risks and open decisions

- **Cost.** Phases 1 to 4 each touch many core files. The prior Fix work took the same
  shape and is the best estimate. Phase 6 needs a new heap representation in C.
- **Elaboration budgets.** The generated-IR cost model is multiplicative for nested
  cases; large constructors or deep tree patterns may hit it (the mutual dispatcher already
  did).
- **Decision: where declarations live.** Context field versus the shared-checked-globals
  environment. The second reuses existing sharing but couples this work to that session's
  `GlobalRef`.
- **Decision: keep or retire the fixed shapes.** Keeping them means two paths to maintain.
- **Out of scope:** indexed families, mutual or nested data, universe-polymorphic data,
  strict-positivity beyond rule 1, and eta or definitional unfolding of data.
