# Initial architecture

Implemented:

- `src/Main.idr`: bootstrap CLI.
- `src/Fibril/Core/Quantity.idr`: quantity representation only, not a usage checker.
- `src/Tests/Main.idr`: representation smoke tests.

Planned boundaries:

- Surface parser and elaborator -> explicit checked quantitative cubical core.
- Foundation-specific syntax/evaluation/conversion/checking behind clear modules.
- Separate reference evaluation and compiled runtime execution.
- Justified erasure -> backend-neutral runtime IR -> C / JavaScript.
- Shared compiler service -> LSP -> Neovim first, VS Code later.

Extract foundation/backend interfaces against real implementations rather than
inventing a universal interface prematurely. Keep source locations and structured
errors available for future IDE services.
