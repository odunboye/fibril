# Initial architecture

Implemented:

- [Internal finite variants](finite-variants.md): nonempty ordered nullary/payload descriptors, positional constructors, erased dependent motives and exhaustive case branches; quantity checking joins branch demands. Structural scope proofs, counters and full/head reduction include the primitive. This is not source data syntax or recursive inductive checking.

- `src/Fibril/Source/Diagnostic.idr`: bounded, escaped scalar-point excerpts; no invented core spans or LSP coordinates.
- `src/Fibril/Source/Syntax.idr`: named expression AST with spans.
- `src/Fibril/Source/StringLiteral.idr`: shared quoted-data decoding for ordinary String atoms and console literals; retains spelling/escapes and located failures.
- `src/Fibril/Source/Global.idr`: closed definitions and declared-signature-preserving lookup through checked ascriptions.
- `src/Fibril/Source/Primitive.idr`: small IO primitive boundary, without putStrLn.
- `src/Fibril/Driver/Prelude.idr`: parse/core-check bundled library definitions.
- `stdlib/Prelude.fib`: actual Fibril putStrLn/pure/bind definitions.
- `src/Fibril/Core/Limits.idr`: shared checking/type-reduction defaults; Driver.Limits re-exports them for compatibility.
- `src/Fibril/Driver/Console.idr`: pure typed IO-description planning before any host action executes.
- `src/Fibril/Effect/Console.idr`: pure action data, separate from ordinary terms.
- `src/Fibril/Runtime/Console.idr`: host stdout adapter and first-error action sequencer; no core normalization hooks.
- `src/Fibril/Driver/Run.idr`: validate whole source, then execute console actions; failures do not execute prefixes.
- `src/Fibril/Source/Rename.idr`: pure same-file edit previews with candidate reparsing, shifted-reference comparison, and conservative capture/entry/size checks; no mutation.
- `src/Fibril/Source/Navigation.idr`: AST-scoped same-document definitions and grouped reference queries over original name-token spans, without type checking.
- `src/Fibril/Source/Symbol.idr`: reusable syntax-only document symbols over source Strings, preserving real name-token spans.
- `src/Fibril/Driver/Symbols.idr`: bounded-file symbols service and versioned JSON output; no semantic checking.
- `src/Fibril/Runtime/Path.idr`: POSIX canonical-path host adapter; not a language FFI or atomic filesystem guarantee.
- `src/Fibril/Driver/ModuleCheck.idr`: dependency-first closed interface checking, direct qualified exports, conservative pre-clone expansion admission, and source-aware human errors.
- `src/Fibril/Driver/ModuleGraph.idr`: bounded canonical dependency discovery, syntax snapshots, and dependency-first graph inspection; not imported checking.
- `src/Fibril/Source/Document.idr`: shared expression/declaration/module metadata parsing with original tokens and header/import/export spans; no filesystem loader.
- `src/Fibril/Source/Declaration.idr`: authored declaration/record grammar and binding-site quotas, with ordinary-only legacy adapters; no record expansion or elaborator dependency.
- `src/Fibril/Source/Format.idr` / `Source/Shape.idr`: conservative source-token gap formatting with reparsing and structural comparison, distinct from IR printing and checking.
- `src/Fibril/Source/Declaration/Syntax.idr`: authored record ASTs, actual binding sites, and lowered named IR data.
- `src/Fibril/Elaboration/Interface.idr`: interface layout schemas, scoped local lookup and exported schema data; imported metadata is published only after dependency checking.
- `src/Fibril/Elaboration/Declaration.idr`: schema-guided named method-block lowering, declaration admission, record expansion, source origins and ordinary typed-let lowering for the compiler pipeline.
- `src/Fibril/Source/Parser.idr`: bounded expression grammar with flat Unit-result do sequencing.
- `src/Fibril/Source/Resolve.idr`: compatibility facade for contextual expression elaboration; arbitrary untyped name-vector entrypoints retain lexical behavior.
- `src/Fibril/Elaboration/Expression.idr`: contextual names-to-core elaboration, typed lets/do lowering and bounded constant/dependent motive inference for typed unary/binary patterns; original core values still need independent checking.
- `src/Fibril/Elaboration/Expression/Scope.idr`: partial scope transport and saturated substitution/type counting for untrusted inference.
- `src/Fibril/Elaboration/Expression/Dictionary.idr`: structural constraint validation and explicit/unique visible-local dictionary requests; opt-in unique visible implementation lookup with canonical alias identities; no recursive instance construction or core rule.
- `src/Fibril/Elaboration/Expression/Parameters.idr`: bounded structural recovery of erased constructor-prefix arguments from checked scrutinee types; no core metavariables, phantom guesses or general implicit search.
- `src/Fibril/Source/Resolve/Error.idr`: lexical versus contextual-elaboration failures at actual scalar source points.
- `src/Fibril/Driver/JSON.idr`: shared escaped JSON strings, objects, positions, and protocol envelope.
- `src/Fibril/Driver/Reference.idr`: tagged built-in documentation and real bundled Prelude definition snapshots, with lexical shadowing and no guessed primitive source locations.
- `src/Fibril/Driver/ProjectNavigation.idr`: checked project definition preparation and version-2 source-aware targets, sharing generic lexical traversal with same-file navigation.
- `src/Fibril/Driver/ProjectReport.idr`: version-2 project check reporting with source snapshots, real file identities, scalar/byte separation, and no v1 location coercion.
- `src/Fibril/Driver/CheckReport.idr`: structured check outcomes with genuine frontend points and explicitly unlocated core/file failures.
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
- [Declaration elaboration](elaboration.md): authored syntax is parsed separately from record expansion; a dedicated admission/lowering pass produces named IR for resolution/checking. elaborate PATH inspects unchecked IR.
- [Dependent record foundations](records.md): core Sigma/PairValue formation and construction with dependent fields and quantitative usage; consuming dependent elimination, unary wrappers and resource-budgeted record telescopes are implemented; erased parameters and explicit consuming patterns are supported; explicit safe projections are supported; dot-field syntax and nominality remain pending.
- `src/Fibril/Core/Runtime.idr`: experimental ordinary runtime usage checking layered over erased typing; not backend execution or cubical checking.
- `src/Fibril/Core/Erased.idr`: experimental erased ordinary context formation, inference/checking, and bounded beta type comparison; no runtime or cubical term checking.
- `src/Fibril/Core/Compatibility.idr`: directional literal-universe acceptance after normalization; separate from beta conversion.
- `src/Fibril/Core/WeakHead.idr`: bounded outer type exposure without reducing annotations/bodies; used for checker shape inspection only.
- `src/Fibril/Core/Reduction.idr`: reference beta stepping and bounded comparison with explicit inconclusive results; not typed conversion.
- `src/Fibril/Core/Context.idr`: scoped telescope storage, dependent lookup, and whole-context coefficient validation; no well-formedness checker.
- `src/Fibril/Core/Usage.idr`: mode coefficients, scope-length-indexed usage vectors, and local binder discharge; not a term checker.
- `src/Fibril/Core/Term.idr`: scoped ordinary terms, renaming, capture-avoiding substitution, and structural equality; no typing or conversion checker.
- `editors/vim/`: optional lexical highlighting, buffer settings, and manually invoked saved-buffer CLI navigation; no LSP or automatic compiler execution.
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
