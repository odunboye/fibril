# Documentation policy

Documentation is part of each meaningful task and commit.

## Declarations and modules

- Document public API declarations with Idris `|||` comments: purpose, important
  inputs, invariants, failure behavior, and limitations where applicable.
- Explain constructor/record semantics when not obvious from the enclosing type.
- Add a module overview describing responsibility, dependencies, and trust boundary.
- Cite stable bibliography keys from `docs/references.md` in relevant code,
  and link theory sections from design pages. Distinguish background, adopted
  rules, and algorithm provenance; a citation is not a correctness proof.
- Explain why non-obvious implementation choices exist; link relevant specification
  sections or published sources. Avoid comments that only restate syntax.
- Distinguish checked proofs, executable tests, proposals, and unsupported features.
- State resource/performance limitations, especially exponential reference solvers.

## Per-task checklist

1. Implement and document the change together.
2. Add regression/negative tests; include an example when it helps users.
3. Update architecture, specification, and examples if their claims changed.
4. Run `make test`, `make examples`, and `make docs`.
5. Inspect generated documentation when changing API structure.
6. Commit code, tests, and documentation as one meaningful task.

Do not claim logical consistency, verified erasure, bounded stack, or timing
guarantees without supporting evidence. Keep proposal status visible.

## Textbook maintenance

- Keep teaching chapters in `docs/book/` and navigation in `docs/book.json`.
- Explain motivation, representation, algorithms, and boundaries.
- Include learning goals, source-reading exercises, and theory links.
- Preserve detailed references and historical decisions separately.
- Update teaching chapters when behavior changes; they complement API contracts.
- Run `make handbook` for local file-link, chapter-navigation, and search-index checks.
- Keep reading assets local and progressively enhanced; core content must remain
  usable without JavaScript. Preserve focus visibility, reduced-motion support,
  and readable mobile/print layouts when changing the theme.

## Generated reference

`make docs` runs Idris 2's `--mkdoc fibril.ipkg` after a pack build.
Open `build/docs/index.html`. Generated files are ignored, not hand-edited.

The docs command uses `IDRIS2` (default: the executable on PATH). It must match
the compiler selected by the pinned pack collection; use
`make docs IDRIS2=/path/to/matching/idris2` when necessary. This environment
requirement is not automatically enforced yet.

Generated API pages complement tutorials, design records, and the specification.

## Checks and current limits

Implemented: API generation, test execution, and runnable bootstrap examples.

Review-time policy: public documentation coverage and link accuracy.
The handbook build checks local file links outside API internals. External URLs,
fragments, and undocumented-export coverage are not automatically checked.
Documentation generation alone does not enforce complete documentation coverage.
Run `make handbook` when changing handbook text, source links, or diagrams.
Proposed Fibril examples remain explicitly unexecutable until the compiler exists.
Future CI should run the same commands and add reliable coverage/link checks.

Docs must track releases and preserve older versions once releases exist.
