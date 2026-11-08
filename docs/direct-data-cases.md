# Direct cases for data

## Use cases

**Implemented first slice:** consume a finite `Sum`, `Optional`-style data type,
or request choice without encoding it as a function or requesting a named
eliminator. Pattern branches can share an ambient linear resource: each
alternative uses it in its own branch, and the ordinary runtime checker joins
those alternative demands. This adds source convenience over existing core
nominal/variant cases. It also supports one-step matching of Nat and the fixed unary
recursive and parameterized list shapes. A Nat successor predecessor is linear
and must be used exactly once, even for an unrestricted scrutinee; this is not itself a recursive
definition or a soundness theorem. Prefer `Bool` for a choice without payload or a record when
all fields exist together. A named eliminator remains an explicit alternative,
but its unrestricted branch arguments cannot capture ambient linear values.

~~~fibril
data Sum (0 A : Type 0) (0 B : Type 0) : Type 0 where
  Left : (1 value : A) -> Sum A B
  Right : (1 value : B) -> Sum A B

render : (1 prefix : String) -> (1 message : Sum String Bool) -> String
render prefix message =
  case message of
    Right flag => if flag then appendString prefix "yes" else appendString prefix "no"
    Left value => appendString prefix value
~~~

A nominal data type with exactly one constructor can be matched on one line
with the inferred-field form, `case h of Open log => log`. The parser cannot
tell this from a record pattern, so the elaborator tries the record reading
first and falls back to the data case; the payload usage rules are unchanged.

The [runnable example](../examples/modules/direct-data-case/Main.fib) uses both
constructors, reverses branch order and also defines a generic `fold` over erased
type parameters. Run from the compiler project:

~~~sh
fibril run --source-dir examples/modules/direct-data-case examples/modules/direct-data-case/Main.fib
~~~

It prints `L: hello`, `R: yes`, then `no`. A separate
[recursive-data example](../examples/modules/recursive-data/Main.fib) removes
one layer of an imported unary recursive family, then uses its fold. The
[recursive-list example](../examples/modules/recursive-list/Main.fib) matches a
linear head and tail before folding the tail. The [request API](../test/fixtures/packages/request-api/src/Mail/Request.fib) exercises
three email-service alternatives locally and from a qualified-import test package;
it is a pure model, not an email server. The separate
[sum-client package](../examples/packages/sum-client/src/Main.fib) directly
imports the external [sum-library](../examples/packages/sum-library/src/Data/Sum.fib)
and matches `Data.Sum.Left`/`Data.Sum.Right` without requesting its eliminator.
Run `fibril run --package examples/packages/sum-client/fibril.yaml` from the
compiler project. A separate [dependent-motive
example](../examples/modules/direct-data-case-dependent/Main.fib) defines a
family indexed by a finite choice and returns a different value type per branch.

## Multi-field constructors

A constructor with two or more fields stores them as one right-nested pair
payload. A direct arm for it must bind exactly one name per field:

~~~fibril
data User : Type where
  Guest : User
  Customer : (email : String) -> (password : String) -> User
  Staff : (email : String) -> User

describe : (1 user : User) -> String
describe user = case user of
  Guest => "guest"
  Customer email password => appendString "customer " email
  Staff email => appendString "staff " email
~~~

The [runnable example](../examples/modules/multi-field-case/Main.fib) also
matches a four-field constructor with linear fields. Elaboration builds the
branch as a payload lambda over nested `PairCase` eliminations, one level per
extra field (the same shape as the named eliminator's branches), so no new core
term is introduced and the core checker validates the result independently.

- Each bound name has the field's declared quantity, so a linear field must be
  used exactly once and an unrestricted one may be unused. The linear payload and
  intermediate tails are consumed by the generated eliminations.
- The arm's constructor must build exactly the scrutinee's nominal type and
  shape with exactly that many fields; a different type's constructor, a wrong
  arity, a missing or duplicate constructor are rejected.
- Result types are inferred as for unary arms: an expected type or `return`
  motive gives a dependent motive, otherwise the result must not depend on a
  field (use an explicit motive when it does).
- A trailing catch-all clause covers a multi-field constructor by destructuring
  its payload: `_` drops the fields and a name (`other => ...`) rebuilds the
  value from them through an unrestricted binding. Either way every field must
  be unrestricted or erased; a linear field is rejected by the usual
  binder-usage check, so name such constructors explicitly.
- A pattern must bind exactly as many names as the constructor has fields;
  otherwise elaboration reports "has N field(s) but the pattern binds M".
- Patterns are flat. Nested patterns and typed binders inside arms remain
  unsupported. Function clause groups accept the same patterns in
  [parenthesized form](function-equations.md#multi-field-clause-patterns).

![Direct case checking boundary](diagrams/direct-data-cases.svg)

## Source form and scope

- Write `case value of` and an aligned, indented multiline branch block when
  [motive inference](data-motive-inference.md) applies, including supported
  expected-dependent results in named equations. Otherwise write
  an explicit erased motive after `return` before `of`. Constructor patterns use a visible local or
  qualified direct-import name: `Missing => ...`, `Text x => ...`,
  `Data.Sum.Left x => ...`, or `Prepend head tail => ...` for a list shape.
  Bodies may continue on more-indented lines; grouped and nested cases work.
- A direct block is recognized when its first arm is nullary or it contains at
  least two aligned arms. A *single unary or binary* pattern remains the existing
  record pattern syntax; use the named eliminator for a one-constructor data type.
  This deliberate disambiguation preserves existing record programs.
- Parenthesized data-header parameters remain explicit at construction sites;
  braced headers can opt constructors into [implicit parameters](data.md). The
  case derives actual nominal arguments from the scrutinee and applies them when
  checking branch names; generic erased type parameters are supported.
- This slice supports nullary, **single-field** and **multi-field** nominal
  constructors, the fixed terminal/unary-self family, and the fixed
  parameterized list shape. A direct list branch binds its head and tail
  **linearly**, while a fold exposes an erased tail plus a linear induction
  result. A multi-field arm binds one name per field, `Customer email password
  => ...`, with each field's declared quantity (see below). No nested patterns,
  constructor wildcard/implicit coverage or general-purpose dependent motive inference is provided.
- This slice runs through named-module project checking (`--source-dir` or
  `--package`); standalone declaration-file checking does not publish the
  checked globals required by these patterns. Local patterns use unqualified
  names; exported constructors from direct imports may be qualified or, if their
  short name is unique, unqualified. Ambiguous names require qualification.
  Package-level direct-dependency permissions and private
  exports still apply. An unqualified local shadow is rejected; qualified names
  are not captured by local binders.
- A pattern name is accepted when its checked global value is definitionally
  the canonical constructor for the exposed family and constructor. Consequently, a
  transparent, unrestricted alias of a constructor can serve as a pattern name;
  it is not a nominal-membership certificate. Duplicate tags, foreign values,
  missing tags, wrong arity and inconclusive conversion fail closed.

The declared data family and constructors must precede their uses and pass
ordinary source-ordered checking. Direct-imported declarations must be exported
and their module must check fully first. Local branch binders and authored
constructor references participate in same-file navigation/rename; existing
single-root project definition can jump from an imported qualified pattern to
its real declaration. The package-aware editor command supports checked package
graphs and validates source and manifest snapshots.
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
   the explicit or inferred motive. The independent existing core checkers validate the
   entire enclosing declaration, including erased-stage restrictions, dependent
   motive, payload use and runtime branch permission joins. No helper application
   or unrestricted branch argument approximates those rules.

For a unary recursive scrutinee, the elaborator instead compares each checked
constructor value with the exact canonical terminal or linear-tail constructor
for that `RecType` key, under guarded node/payload admission. It builds a core
`RecCase`: the terminal branch has no payload and the successor branch receives
the actual tail at quantity 1. The same expected-result abstraction and explicit
motive fallback apply; the independent checker validates the completed term.
The fold remains a different operation: it recursively computes a result and
gives its step only an erased tail.

A list scrutinee builds `SeqCase`, whose cons branch receives both the actual
head and tail linearly. To compare a parameterized checked global with a
canonical constructor, the elaborator first checks that its erased parameter
can accept the exposed element type, then instantiates and compares under
bounded guarded normalization. Specialized transparent aliases are also
accepted if their checked values match. Extra unsolved parameters are not guessed.

The module checker sees earlier checked globals only; later/forward definitions
are unavailable. This first slice does not consume authored `DataSchema` hints;
those remain untrusted metadata, not a source of typing authority.

## Limits and evidence

The parser and case planner admit at most 64 branches; the inferred nominal type
and each constructor global value are admitted at 512 raw core nodes; list-case
constructor instantiation and its canonical head/tail comparison also have a
combined 512-node and character-payload admission, so larger types can require
a different program structure. Normalizing or comparing a constructor uses the
existing 128-step type-reduction fuel.
Existing source/module, 200000-node expanded-core, checker-depth and formatter
budgets remain independent. Inconclusive normalization/comparison is an error,
not a guessed match. These admission policies are not memory, deadline or
metatheory guarantees.

Tests exercise generic Sum, unary and list recursive cases and aliases, both branches,
source-order reversal, dependent motives, ambient linear use on both branches, missing/duplicate/unknown/foreign
patterns, wrong payload arity, omitted/duplicated linear uses, erased payload
misuse, malformed layout, grouped ascriptions, nesting, source navigation,
formatter idempotence, 64/65 parser admission and existing record-case behavior.
They are sampled implementation evidence, not preservation, normalization,
erasure or quantitative/cubical soundness proofs.

Next: general multiple and dependent field patterns, single-pattern
disambiguation and more general dependent motive inference through more contexts.
General recursive data, positivity and structural termination remain separate milestones.
