# Initial architecture

Implemented:

- `src/Fibril/Core/Erased.idr`: experimental erased ordinary context formation, inference/checking, and bounded beta type comparison; no runtime or cubical term checking.
- `src/Fibril/Core/Reduction.idr`: reference beta stepping and bounded comparison with explicit inconclusive results; not typed conversion.
- `src/Fibril/Core/Context.idr`: scoped telescope storage, dependent lookup, and whole-context coefficient validation; no well-formedness checker.
- `src/Fibril/Core/Usage.idr`: mode coefficients, scope-length-indexed usage vectors, and local binder discharge; not a term checker.
- `src/Fibril/Core/Term.idr`: scoped ordinary terms, renaming, capture-avoiding substitution, and structural equality; no typing or conversion checker.
- `src/Main.idr`: bootstrap CLI.
- `src/Fibril/Core/Quantity.idr`: quantity coefficients, arithmetic, and local binder policy; not a usage checker.
- `src/Fibril/Foundation/DeMorgan/Interval.idr`: interval syntax, substitution, endpoint interpretation.
- `src/Fibril/Foundation/DeMorgan/NormalForm.idr`: reference symbolic interval equality.
- `src/Fibril/Foundation/DeMorgan/Face.idr`: separate face lattice, entailment, endpoint extraction, and substitution.
- `src/Fibril/Foundation/DeMorgan/Scope.idr`: checked dimension scoping, interval weakening/substitution/instantiation, and scoped face entailment.
- `src/Fibril/Foundation/DeMorgan/Restriction.idr`: accumulated face assumptions, entailment, weakening, and substitution.
- `test/src/Tests/Main.idr`: deterministic regression runner, followed by Hedgehog properties.
- `test/src/Tests/Properties.idr`: bounded scope-correct generators and structural laws; test-only Hedgehog dependency.
- `test/src/Tests/Erased.idr` and `Reduction.idr`: ordinary checking and reduction regressions.

Planned boundaries:

- Surface parser and elaborator -> explicit checked quantitative cubical core.
- Foundation-specific syntax/evaluation/conversion/checking behind clear modules.
- Separate reference evaluation and compiled runtime execution.
- Justified erasure -> backend-neutral runtime IR -> C / JavaScript.
- Shared compiler service -> LSP -> Neovim first, VS Code later.

Extract foundation/backend interfaces against real implementations rather than
inventing a universal interface prematurely. Keep source locations and structured
errors available for future IDE services.
