# Direct cases for non-recursive data

## Use cases

**Implemented first slice:** consume a finite `Sum`, `Optional`-style data type,
or request choice without encoding it as a function or requesting a named
eliminator. Pattern branches can share an ambient linear resource: each
alternative uses it in its own branch, and the ordinary runtime checker joins
those alternative demands. This adds source convenience over existing core
nominal/variant cases; it does not add recursive data, recursion or a new
soundness theorem. Prefer `Bool` for a choice without payload or a record when
all fields exist together. A named eliminator remains an explicit alternative,
but its unrestricted branch arguments cannot capture ambient linear values.

~~~fibril
data Sum (0 A : Type 0) (0 B : Type 0) : Type 0 where
  Left : (1 value : A) -> Sum A B
  Right : (1 value : B) -> Sum A B

render : (1 prefix : String) -> (1 message : Sum String Bool) -> String
render = \(1 prefix : String) => \(1 message : Sum String Bool) =>
  case message return (\(0 self : Sum String Bool) => String) of
    Right flag => if flag then appendString prefix "yes" else appendString prefix "no"
    Left value => appendString prefix value
~~~

The [runnable example](../examples/modules/direct-data-case/Main.fib) uses both
constructors, reverses branch order and also defines a generic `fold` over erased
type parameters. Run from the compiler project:

~~~sh
fibril run --source-dir examples/modules/direct-data-case examples/modules/direct-data-case/Main.fib
~~~

It prints `L: hello`, `R: yes`, then `no`. The separate
[sum-client package](../examples/packages/sum-client/src/Main.fib) directly
imports the external [sum-library](../examples/packages/sum-library/src/Data/Sum.fib)
and matches `Data.Sum.Left`/`Data.Sum.Right` without requesting its eliminator.
Run `fibril run --package examples/packages/sum-client/fibril.yaml` from the
compiler project. A separate [dependent-motive
example](../examples/modules/direct-data-case-dependent/Main.fib) defines a
family indexed by a finite choice and returns a different value type per branch.

![Direct case checking boundary](diagrams/direct-data-cases.svg)

## Source form and scope

- Write an explicit erased motive after `return`, then `of` and an aligned,
  indented multiline branch block. Constructor patterns use a visible local or
  qualified direct-import name and zero or one field binder: `Missing => ...`,
  `Text x => ...`, or `Data.Sum.Left x => ...`.
  Bodies may continue on more-indented lines; grouped and nested cases work.
- A direct block is recognized when its first arm is nullary or it contains at
  least two aligned arms. A *single unary* pattern remains the existing record
  pattern syntax; use the named eliminator for a one-constructor unary data type.
  This deliberate disambiguation preserves existing record programs.
- Data parameters remain explicit at construction sites. The case derives the
  actual nominal arguments from the scrutinee and applies them when checking
  branch names; generic erased type parameters are supported.
- This slice supports only nullary and **single-field** constructors. Wider
  dependent-field constructors remain usable through named eliminators, but are
  not silently treated as direct one-field patterns. No nested patterns,
  constructor wildcard/implicit coverage or motive inference is provided.
- This slice runs through named-module project checking (`--source-dir` or
  `--package`); standalone declaration-file checking does not publish the
  checked globals required by these patterns. Local patterns use unqualified
  names; imported patterns use the normal qualified names from an explicit direct
  source-module import. Package-level direct-dependency permissions and private
  exports still apply. An unqualified local shadow is rejected; qualified names
  are not captured by local binders.
- A pattern name is accepted when its checked global value is definitionally
  the canonical constructor at that nominal type and tag. Consequently, a
  transparent, unrestricted alias of a constructor can serve as a pattern name;
  it is not a nominal-membership certificate. Duplicate tags, foreign values,
  missing tags, wrong arity and inconclusive conversion fail closed.

The declared data family and constructors must precede their uses and pass
ordinary source-ordered checking. Direct-imported declarations must be exported
and their module must check fully first. Local branch binders and authored
constructor references participate in same-file navigation/rename; existing
single-root project definition can jump from an imported qualified pattern to
its real declaration. Package-aware editor navigation is not yet implemented.
Formatting reparses and compares branch syntax before returning output, and
retains branch alignment.

## Checking and lowering

1. Contextual elaboration infers the scrutinee type with the erased checker,
   weak-head exposes its actual nominal type/variant shape, and applies its
   retained parameter indices to each visible branch global.
2. A bounded normalization exposes the branch tag. Definitional comparison
   checks its closed transparent value against the canonical constructor built
   from the **inferred nominal identity and complete shape**, not merely its
   spelling or an unchecked data schema. Payload quantity/domain come from the
   actual variant descriptor.
3. Every tag must appear exactly once; branches are reordered to descriptor
   order. A payload branch elaborates its body under a binder with that actual
   quantity and domain. Nullary branches receive no fabricated Unit payload.
4. `assembleDataCase` builds an ordinary `NominalCase`/`VariantCase` term with
   the explicit motive. The independent existing core checkers validate the
   entire enclosing declaration, including erased-stage restrictions, dependent
   motive, payload use and runtime branch permission joins. No helper application
   or unrestricted branch argument approximates those rules.

The module checker sees earlier checked globals only; later/forward definitions
are unavailable. This first slice does not consume authored `DataSchema` hints;
those remain untrusted metadata, not a source of typing authority.

## Limits and evidence

The parser and case planner admit at most 64 branches; the inferred nominal type
and each constructor global value are admitted at 512 raw core nodes; normalizing
or comparing a constructor uses the existing 128-step type-reduction fuel.
Existing source/module, 200000-node expanded-core, checker-depth and formatter
budgets remain independent. Inconclusive normalization/comparison is an error,
not a guessed match. These admission policies are not memory, deadline or
metatheory guarantees.

Tests exercise generic Sum, both branches, source-order reversal, dependent
motives, ambient linear use on both branches, missing/duplicate/unknown/foreign
patterns, wrong payload arity, omitted/duplicated linear uses, erased payload
misuse, malformed layout, grouped ascriptions, nesting, source navigation,
formatter idempotence, 64/65 parser admission and existing record-case behavior.
They are sampled implementation evidence, not preservation, normalization,
erasure or quantitative/cubical soundness proofs.

Next: multiple and dependent field patterns, single-unary disambiguation and
motive inference. Recursive data,
positivity and structural termination remain separate milestones.
