# Initial architecture

Implemented:

- `src/Main.idr`: bootstrap CLI.
- `src/Fibril/Core/Quantity.idr`: quantity coefficients, arithmetic, and local binder policy; not a usage checker.
- `src/Fibril/Foundation/DeMorgan/Interval.idr`: interval syntax, substitution, endpoint interpretation.
- `src/Fibril/Foundation/DeMorgan/NormalForm.idr`: reference symbolic interval equality.
- `src/Fibril/Foundation/DeMorgan/Face.idr`: separate face lattice, entailment, endpoint extraction, and substitution.
- `src/Fibril/Foundation/DeMorgan/Scope.idr`: checked dimension scoping, interval weakening/substitution/instantiation, and scoped face entailment.
- `src/Fibril/Foundation/DeMorgan/Restriction.idr`: accumulated face assumptions, entailment, weakening, and substitution.
- `test/src/Tests/Main.idr`: quantity, interval, and face regression tests.

Planned boundaries:

- Surface parser and elaborator -> explicit checked quantitative cubical core.
- Foundation-specific syntax/evaluation/conversion/checking behind clear modules.
- Separate reference evaluation and compiled runtime execution.
- Justified erasure -> backend-neutral runtime IR -> C / JavaScript.
- Shared compiler service -> LSP -> Neovim first, VS Code later.

Extract foundation/backend interfaces against real implementations rather than
inventing a universal interface prematurely. Keep source locations and structured
errors available for future IDE services.
