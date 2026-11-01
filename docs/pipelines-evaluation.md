# Pipelines dependency evaluation

Status: evaluated; adoption deferred. No project dependency was added.

## Source examined

- Repository: https://gitlab.com/glaive-research/pipelines
- Revision: `785aaf0dac6fb68ad71e5f2558d3b94f65087a33`
- Built its `pipelines.ipkg` successfully using Fibril's pinned pack collection
  `nightly-260903`.

A successful Idris build is not evidence that every declaration is hole-free,
total without assertions, or appropriate for trusted proof dependencies.

## Findings

- `Pipeline.Basic` supplies typed pure and monadic sequential composition.
- `Pipeline.Dependent` supports stages indexed by intermediate values.
- The package includes categorical, equality, and functorial machinery.
- `Pipeline.Basic` contains named holes in its unfinished private example,
  including readARg and parseCmd.
- `Pipeline.Functor` contains named holes and assert_total uses.
- `Pipeline.Equality` contains assert_total uses and unfinished examples.
- Other experimental source modules also contain unfinished work. Not every
  question-mark occurrence is an unresolved named hole: some are solved metas.

These findings do not establish that the basic runner is incorrect. They mean
the package needs a narrower review than simply accepting a successful build.
No exhaustive dependency security or correctness audit has been performed.

## Intended boundary

Pipeline orchestration belongs outside the independently callable kernel:

    source -> lexing -> parsing -> elaboration -> checked core
    checked core -> justified erasure -> runtime IR -> backend

Start with monadic pipelines carrying structured diagnostics. Use dependent
pipelines only when indexing materially helps; assess retention of intermediate
values. Incremental compiler/LSP services must remain independently callable,
rather than forcing all requests through one whole-file sequence.

Typed stage connectivity does not prove semantic preservation or kernel
soundness. Tracing and timing infrastructure does not establish real-time bounds.

## Adoption gate

1. Review a minimal upstream revision/subset for holes and unsafe assertions.
2. Prefer an upstream cleanup; otherwise consider a small attributed fork,
   preserving its license and documenting local changes.
3. Pin the chosen full commit through pack.
4. Add a runnable integration example and short-circuit/error propagation tests.
5. Keep pipeline imports out of core syntax, evaluation, and checking modules.
6. Document which parts were audited and any remaining trust assumptions.

Until then, use ordinary explicit function composition for new infrastructure.
Do not silently add the full library or describe deferred integration as complete.
