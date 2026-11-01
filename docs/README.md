# Documentation

## Start with the textbook

Begin with [Chapter 1: Orientation](book/00-orientation.md), then follow
[binding](book/01-binding.md), [resources](book/02-resources.md),
[contexts/reduction](book/03-contexts-reduction.md), [checking](book/04-checkers.md),
[cubical infrastructure](book/05-cubical.md),
[testing/maintenance](book/06-testing-contributing.md), and [roadmap](book/07-roadmap.md).
The generated homepage separates teaching chapters, references, and project records.

## Reference index

- [Expression parser/checking](parser.md): implemented source-to-core checking slice.

- [Expression lexer](lexer.md): token subset, aliases, positions, and next parser boundary.

- [Project/dependency format](packages.md): pubspec-style future manifests; pack remains the bootstrap.

- [Unicode source text](unicode-source.md): validation, positions, and proposed identifier/notation rules.

- [Reference benchmarks](benchmarks.md): reproducible exploratory measurements and limits.

- [Safety and performance](safety-performance.md): present safeguards, risks, and planned benchmarks.
- [Lessons from Zig](zig-lessons.md): allocation, errors, cleanup, specialization, and target design.

- [Prototype CLI](cli.md): built-in checking demo and command limits.

- [Testing](testing.md): deterministic regressions, Hedgehog properties, and replay.

- [Theoretical references](references.md): bibliography and code-to-theory map.

- [Browsable handbook](handbook.md): build, serve, and maintain the offline book.
- [Implementation tour](implementation-tour.md): completed work, diagrams, and selected call graph.

- [Documentation policy](documentation-policy.md): per-task requirements and API generation.
- [Contributing](../CONTRIBUTING.md): development checklist.
- Generated API reference: run `make docs`, then open `build/docs/index.html`.

- [Examples](../examples/README.md): runnable bootstrap project and proposed language scenarios.

- [Design discussion record](design.md): decisions, recommendations, open questions.
- [Pipelines evaluation](pipelines-evaluation.md): dependency inspection, findings, and adoption gate.
- [Experimental runtime-usage checker](runtime-checker.md): ordinary resource accounting and restrictions.
- [Experimental erased checker](erased-checker.md): implemented ordinary type checking and explicit limits.
- [Reference reduction](reduction.md): beta steps, fuel, conversion outcomes, and limitations.
- [Ordinary checking plan](ordinary-checking.md): context formation, dependent lookup, typing outline, and conversion gates.
- [Initial core draft](core-draft.md): proposed grammar, quantity accounting, and unresolved rules.
- [Foundation baseline](foundation-baseline.md): CCHM reference and unresolved quantitative obligations.
- [First milestone](milestone-01.md): core-checker scope and acceptance criteria.
- [Guarantees and non-guarantees](guarantees.md).
- [Architecture](architecture.md).

Planned: getting started, language tutorial/reference, HoTT guide, platform guides,
generated library reference, contributor workflow, and versioned specification/RFCs.
Documentation examples will be checked as the necessary tooling becomes available.
