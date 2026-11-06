# Documentation

## Learn to program

Start with the [Programming in Fibril tutorial](tutorial/README.md) for a
hands-on introduction to the language and its current limitations.

## Learn the implementation

Begin with [Chapter 1: Orientation](book/00-orientation.md), then follow
[binding](book/01-binding.md), [resources](book/02-resources.md),
[contexts/reduction](book/03-contexts-reduction.md), [checking](book/04-checkers.md),
[cubical infrastructure](book/05-cubical.md),
[testing/maintenance](book/06-testing-contributing.md), and [roadmap](book/07-roadmap.md).
The generated homepage separates teaching chapters, references, and project records.

## Reference index

- [Implicit arguments](implicit-arguments.md): infer erased prefixes on direct checked global calls.

- [Experimental checked C emission](native-c.md): compile a supported console subset without precomputing output.

- [Direct non-recursive data cases](direct-data-cases.md): exhaustive local or qualified zero/unary matches with linear branch joins.

- [Data-case motive inference](data-motive-inference.md): omit `return` for supported constant and expected-dependent results.

- [Named function equations](function-equations.md): inherit parameter domains and quantities from explicit signatures.

- [Bare Type](bare-type.md): notation for Type 0, with explicit higher universes unchanged.

- [Pure String values](strings.md): ordinary typing/data and the separate console effect boundary.

- [Neovim/Vim highlighting](editor-highlighting.md): local runtime setup, lexical scope, and optional tests.

- [Hello world / hosted console](console-runner.md): first run command and its explicit effect boundary.
- [Binary transport pilot](io-binary.md): internal byte-preserving hosted/native IO, accounting contracts and source API gates.

- [Source-ordered declarations](declarations.md): explicit headers lowered to typed lets, not transparent globals.

- [Fuel and resumable normalization](reduction-fuel.md): exact budget laws and raw-tag boundaries.

- [Instantiation and root beta laws](beta-laws.md): structural proofs tied to the actual reducer.

- [Substitution composition](substitution-composition.md): mixed fusion and weakening/instantiation proofs.

- [Basic substitution laws](substitution.md): congruence, variable correspondence, and identity.

- [Structural renaming laws](renaming.md): host-checked proofs and their exact scope.

- [Located frontend diagnostics](diagnostics.md): bounded excerpts and structured driver errors.

- [Permission joins](alternatives.md): local proof and branching admissibility.

- [Booleans and conservative branching](boolean.md): checked alternatives without general subusage joining.

- [Primitive Unit](unit.md): first data value and explicit quantity limitations.

- [Checked reference evaluation](evaluation.md): source checking followed by bounded normalization.

- [Python interoperability](python-interop.md): worker and optional embedded CPython architecture.

- [Cumulativity and dependent rewriting](cumulativity-rewriting.md): staged rules, implementation gates, and safeguards.

- [Expression parser/checking](parser.md): implemented source-to-core checking slice.

- [Expression lexer](lexer.md): token subset, aliases, positions, and next parser boundary.

- [Project/dependency format](packages.md): local manifest contract; pack remains the bootstrap.
- [Libraries and tests](libraries-and-tests.md): standalone inventories and checked pure Bool suites, with --lib scaffolding.
- [Local packages](local-packages.md): canonical explicit dependency closure and real multi-root check/run.
- [Strict manifest inspection](manifests.md): maintained YAML parsing and strict local schema, without dependency/source loading.

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
