# Initial architecture

Implemented:

- `src/Fibril/Source/Diagnostic.idr`: bounded, escaped scalar-point excerpts; no invented core spans or LSP coordinates.
- `src/Fibril/Source/Syntax.idr`: named expression AST with spans.
- `src/Fibril/Source/Declaration.idr`: column-one signature/definition framing, source-order scope, fixed main entry, and typed-let lowering; no transparent globals/modules.
- `src/Fibril/Source/Parser.idr`: bounded expression grammar, no declaration/layout parsing.
- `src/Fibril/Source/Resolve.idr`: lexical names to scoped core and checked-as-identity ascriptions and nonrecursive typed-let elaboration, no globals.
- `src/Fibril/Driver/Check.idr`: source frontend/checker orchestration and shared runtime-source preparation.
- `src/Fibril/Driver/Evaluate.idr`: check-before-reduction reference evaluation and post-reduction type/resource validation.

- `src/Fibril/Source/Lexer.idr`: minimal expression tokens, retained spelling, and scalar spans; no layout or parser.
- `src/Fibril/Source/UTF8.idr`: strict scalar decoding with malformed-byte offsets; no lossy replacement.
- `src/Fibril/Source/File.idr`: bounded raw-file IO, exact-read/growth checks, decoding and control validation, represented-result cleanup.
- `src/Fibril/Source/Text.idr`: decoded-source validation with scalar positions; not byte decoding, lexing, or identifier approval.

- `src/Fibril/Core/Substitution/Instantiation.idr`: naturality of instantiation under renaming/substitution.
- `src/Fibril/Core/Reduction/Fuel.idr`: resumable-result host API and total fuel/stability/no-next-step proofs.
- `src/Fibril/Core/Reduction/Beta.idr`: host-checked compatibility for the actual known-root beta step, not general strategy commutation.
- `src/Fibril/Core/Substitution/Composition.idr`: total mixed-fusion, composition, and weakening/instantiation syntax laws.
- `src/Fibril/Core/Substitution.idr`: total pointwise/variable-correspondence laws; derives substitution identity from renaming.
- `src/Fibril/Core/Renaming.idr`: total host-checked structural laws, separate from runtime checking/reduction.
- `src/Fibril/Core/Pretty.idr`: shared explicit-term diagnostics; no parsing or evaluation.
- `src/Fibril/Core/Runtime.idr`: experimental ordinary runtime usage checking layered over erased typing; not backend execution or cubical checking.
- `src/Fibril/Core/Erased.idr`: experimental erased ordinary context formation, inference/checking, and bounded beta type comparison; no runtime or cubical term checking.
- `src/Fibril/Core/Compatibility.idr`: directional literal-universe acceptance after normalization; separate from beta conversion.
- `src/Fibril/Core/WeakHead.idr`: bounded outer type exposure without reducing annotations/bodies; used for checker shape inspection only.
- `src/Fibril/Core/Reduction.idr`: reference beta stepping and bounded comparison with explicit inconclusive results; not typed conversion.
- `src/Fibril/Core/Context.idr`: scoped telescope storage, dependent lookup, and whole-context coefficient validation; no well-formedness checker.
- `src/Fibril/Core/Usage.idr`: mode coefficients, scope-length-indexed usage vectors, and local binder discharge; not a term checker.
- `src/Fibril/Core/Term.idr`: scoped ordinary terms, renaming, capture-avoiding substitution, and structural equality; no typing or conversion checker.
- `src/Main.idr`: CLI argument dispatch and IO.
- `src/Fibril/Driver/Demo.idr`: built-in checking/algebra demo orchestration outside the core.
- `src/Fibril/Core/Quantity.idr`: quantity coefficients, arithmetic, and local binder policy; not a usage checker.
- `src/Fibril/Foundation/DeMorgan/Interval.idr`: interval syntax, substitution, endpoint interpretation.
- `src/Fibril/Foundation/DeMorgan/Sorted.idr`: sorted canonicalization and merge subset helpers; ascending-input precondition.
- `src/Fibril/Foundation/DeMorgan/NormalForm.idr`: reference symbolic interval equality.
- `src/Fibril/Foundation/DeMorgan/Face.idr`: separate face lattice, entailment, endpoint extraction, and substitution.
- `src/Fibril/Foundation/DeMorgan/Scope.idr`: checked dimension scoping, interval weakening/substitution/instantiation, and scoped face entailment.
- `src/Fibril/Foundation/DeMorgan/Restriction.idr`: accumulated face assumptions, entailment, weakening, and substitution.
- `test/src/Tests/Main.idr`: deterministic regression runner, followed by Hedgehog properties.
- `test/src/Tests/RuntimeProperties.idr`: constructive linear-capture examples and sampled preservation/rejection properties in a fixed open context.
- `test/src/Tests/TypedProperties.idr`: bounded constructive erased term/type pairs, preservation/conversion tests, and classifications.
- `test/src/Tests/Reference/`: frozen pre-optimization DNF solver oracles, independent of shared production helpers.
- `test/src/Tests/Properties.idr`: bounded scope-correct generators and structural laws; test-only Hedgehog dependency.
- `test/src/Tests/Erased.idr` and `Reduction.idr`: ordinary checking and reduction regressions.

Optional foreign-runtime experiment:

- `experiments/python-embed/`: standalone CPython C adapter and embedding tests;
  no core imports, generated-C integration, or mandatory Python runtime dependency.
- `tools/test_python_embed.py`: explicit opt-in build; no package installation.

Benchmark infrastructure:

- `bench/bench.ipkg`: separate pack project depending on the core library.
- `bench/src/Workloads.idr`: fixed, result-validated workloads.
- `bench/src/Main.idr`: bounded argument handling and monotonic batch timing.
- `tools/benchmark.py`: explicit Chez build, repeat samples, and metadata reports.
- `tools/test_benchmark.py`: structural/invalid-input checks, not speed thresholds.

Planned boundaries:

- Surface parser and elaborator -> explicit checked quantitative cubical core.
- Foundation-specific syntax/evaluation/conversion/checking behind clear modules.
- Separate reference evaluation and compiled runtime execution.
- Justified erasure -> backend-neutral runtime IR -> C / JavaScript.
- Shared compiler service -> LSP -> Neovim first, VS Code later.

Extract foundation/backend interfaces against real implementations rather than
inventing a universal interface prematurely. Keep source locations and structured
errors available for future IDE services.
