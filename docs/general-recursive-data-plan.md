# General recursive data: plan

**Status: phases 1 and 2 are implemented (core terms, reduction, declaration admission);
phases 3 onward are not.** It records what restricts recursive
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
| 3 | Typing in `Erased` and `Runtime` (dependent motive, exhaustive, quantity joins), reduction and weak head | termination |
| 4 | Evaluation (`Evaluation.idr`) and `Extract.idr`: fields of a branch are smaller than the scrutinee | native support |
| 5 | Source: `data` declarations beyond the fixed shapes, constructor application, `case`, pattern equations | pattern-clause groups |
| 6 | Native emission and runtime values (`Emit.idr`, `fibril_runtime.c`) | scale |
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
