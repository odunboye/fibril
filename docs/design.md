# Fibril — design discussion record

Status: initial design record, not an implemented language or a soundness claim.
This document captures the conversation's decisions, recommendations, and open questions.

## 1. Identity and goals

- Name: **Fibril**. Cohera was briefly considered and then replaced with Fibril.
- Implementation language: **Idris 2**.
- Purpose: practical programming and mathematics/proofs, including HoTT.
- Development strategy: a careful path toward a practical language rather than a disposable educational prototype.
- Surface language: familiar to Idris 2, indentation-based; retain familiar declarations, implicit arguments, interfaces, and pattern matching where compatible with the foundations.
- Proofs and programs are unified, as in Idris. No separate proof language or mandatory proof/program module division.
- Seek usability improvements through tooling and diagnostics rather than hiding important distinctions.
- Domain is unresolved. fibril.dev was registered at the time of discussion; fibrilang.dev returned no registry record. Neither current availability nor affordable registration/renewal pricing is established.

## 2. Foundations — decisions

- Use **cubical type theory**, initially a **De Morgan** foundation in the CCHM tradition.
- Goal: computational univalence, paths, transport, and eventually selected higher inductive types.
- Choose a specific published calculus before fixing kernel rules. Cubical Agda is a practical reference, not a specification to mix freely with other calculi.
- Support alternative foundations through implementation boundaries and eventually an interface.
- Foundation selection is project-wide.
- Switching foundations means re-elaborating and rechecking source, not mixing foundations within a program.
- Record the foundation in artifacts; incompatible artifacts cannot be reused.
- Shared source portability must be checked, not assumed. Foundation-specific features may need source changes.
- Implement De Morgan first; refine abstractions against a real second implementation rather than overgeneralizing upfront.
- Do not require every foundation to provide De Morgan-specific interval operations.

Discussed alternatives: Cartesian cubical type theory; higher observational type theory as a neighboring, more research-oriented approach rather than another interchangeable cubical calculus.

Open: exact calculus, universe rules, inductive/HIT rules, and the relationship between Idris-style equality/Refl/rewriting and cubical paths. Definitional equality, paths, and decidable Boolean equality must remain distinct.

## 3. Quantities — decision

Support Idris-style quantities **from the outset**:

- `0`: erased.
- `1`: linear, used exactly once under the specified checking rules.
- Unrestricted: repeatable use.

This includes linear resource management, not merely erasure. Quantities must be designed together with cubical checking, not bolted on later.

Open: sound interaction of linearity with composition, transport, substitution, erasure, and borrowing. Idris's quantitative rules cannot simply be presumed compatible with a cubical core.

## 4. Totality and trust — decisions

The final preference supersedes the earlier partial-by-default discussion:

- **Total by default**, including termination and exhaustive pattern coverage.
- Explicit escape hatch for partial computations, using familiar `partial` syntax as a proposal.
- Partial computations must not establish trusted proofs or hide behind unchecked wrappers.
- Separate partiality from unsafe logical assertions and axioms.
- Track unsafe assumptions and relevant dependencies transitively.
- A looping term of type Void is not a valid trusted proof.

A sound restriction on partial computation in types/proofs remains to be specified. Totality is not a deadline guarantee. Long-running IO requires a precise effect/guarded-execution model; it should not be treated as proof of termination of external execution.

Consistency of the combined design has not been established.

## 5. Architecture — recommendations

- Small trusted kernel; elaborate implicit arguments, pattern matching, and tactics into explicit terms checked by it.
- Separate type-checking evaluator from compiled runtime.
- Explore normalization by evaluation appropriate to the selected cubical calculus.
- Expose core terms and theorem dependencies for inspection.
- Maintain a reference evaluator and compare compiled results against it.
- Keep a feature-interaction matrix and regression tests.

Suggested pipeline:

    Source
      -> elaborated quantitative cubical core
      -> checking and justified compilation/erasure
      -> shared runtime IR
      -> C or JavaScript

Foundation selection and compilation backend selection are independent.

## 6. Backends — decisions

**C and JavaScript are first-class initial targets.** C is the native default; web projects use JavaScript. Other backends may follow.

- C: native executables, CLI tools, servers, embedded.
- JavaScript: browsers, potentially Node.js.
- Shared semantics, with explicit platform libraries and FFI capabilities.
- C-specific runtime representations stay out of the logical core.
- Specify integers, overflow, division, strings/Unicode, evaluation order, foreign exceptions, and tail calls consistently.
- Avoid C undefined behavior and JavaScript precision loss.
- Do not rely on C compiler tail-call optimization.

Earlier Scheme-first recommendation was superseded by the C/JS decision.

## 7. Runtime and erasure

- Types and quantity-0 arguments may be erased only under justified rules.
- Do not erase all proofs or paths indiscriminately: computational transport/univalence can affect results.
- Initially preserve more relevant information rather than optimize unsafely.
- Hosted memory-management strategy remains open. GC was recommended; Boehm was discussed but not selected.
- Linearity does not automatically eliminate GC or guarantee cleanup.
- Closure representation, arbitrary-precision numbers, calling conventions, panic behavior, and allocation accounting need specification.

## 8. Web development — agreed direction

1. Typed JavaScript interoperability first.
2. A small typed browser library for DOM/events and listener cleanup.
3. Framework adapters when useful.
4. A Fibril-native UI library only when experience justifies it.

Interop should address modules, objects, callbacks, promises, null/undefined, ownership, and lifetimes. Foreign data needs runtime validation before being treated as verified Fibril values; declarations alone are not validation.

## 9. Embedded — decisions

Embedded support shapes the architecture from the outset.

Targets: **ARM Cortex-M and ESP32**. The later ARM/ESP32 clarification superseded ARM/STM32 as the stated target pair; specific boards remain undecided. ESP32 variants are Xtensa or RISC-V, not ARM.

Support both profiles:

### Predictable bare metal

- No required OS, heap, GC, or implicit runtime scheduling.
- Static/caller-provided storage and bounded pools.
- Supported no-heap subset; reject hidden allocating operations there.
- Fixed-width arithmetic, bit operations, explicit overflow behavior.
- Controlled layout, alignment, startup, linking, panic, volatile access, and intrinsics.
- Explicit interrupts and peripheral/buffer ownership.
- Allocation and stack visibility; stack-conscious compilation.

### Hard real-time

Adds bounded execution, stack, blocking, and interference requirements on deadline-critical paths, plus target-specific timing evidence.

- No unbounded allocation or GC on critical paths.
- Bounded loops/recursion and auditable foreign calls.
- Analyze interrupts, scheduling, contention, caches, and multicore effects.
- Wireless/vendor runtime behavior on ESP32 may require restrictions or isolation.
- Timing claims depend on board, toolchain, configuration, and application assumptions.
- Supporting hard-real-time development is not itself a verified deadline guarantee.

Recommended first slice: one Cortex-M board, no-heap GPIO example, static buffer, linear peripheral handle, checked pure-logic property; then a bounded task with timing evidence, followed by ESP32.

Open: chips/boards, deadlines, wireless requirements, bare-metal vs RTOS integration, and timing-analysis tools.

## 10. Learning from existing languages

### Idris 2

Syntax, quantities, dependent pattern matching, interfaces, and practical compilation.

### Agda

Recommendations:

- First-class cubical checking/computation for paths, transport, univalence, and higher inductive types; use a published calculus as the specification.
- Interactive holes, goal refinement, case splitting, and local contexts augmented with quantities and cubical boundary obligations.
- Specify coverage, impossible cases, termination, and dependent pattern matching through elaboration into checked core terms.
- Visible module safety boundaries: totality, axioms, unsafe dependencies, and foundation requirements.
- Predictable inference with explicit annotations, bounded search, and explanations of stuck checking.

### Lean 4

Recommendations:

- Incremental elaboration preserving source locations, goals, constraints, and partial checking results; support cancellation and correct cache invalidation.
- Tactics, deriving, and search produce kernel-checked ordinary terms; start with small reliable operations.
- Hygienic syntax expansion and inspectable elaboration into a stable core rather than arbitrary kernel extensions.
- Controlled simplification and rewriting with explicit rewrite sets, search traces, and execution limits; rules must respect quantities and cubical equality.
- Integrated package/build tooling, consistent library naming, documentation, tests, and discoverable APIs.

Do not copy Lean's proof-irrelevant Prop semantics or either system's equality machinery wholesale. Avoid unrestricted metaprogramming, large automation frameworks before diagnostics, and assuming their resource models meet Fibril's linear/embedded requirements.

### Coq / Rocq

Proof engineering, explicit trust boundaries, automation, modularity.

Avoid importing incompatible assumptions such as unrestricted proof irrelevance or uniqueness of identity proofs into higher-path reasoning.

### Rust

Recommended lessons, not all finalized language features:

- Explicit ownership at boundaries and carefully scoped borrowing.
- Distinguish Rust's largely affine ownership from Fibril's exact-use linear quantity.
- Prevent borrowed references escaping owners and conflicting mutable accesses.
- Encapsulate unsafe memory/hardware operations behind audited safe APIs.
- Keep runtime unsafety separate from permission to assert logical axioms.
- Layer libraries into core/no mandatory allocation, allocator-dependent, and platform-specific functionality.
- Prefer Result-style errors and explicit propagation initially.
- Specify cleanup on success, failure, panic, and cancellation; bounded cleanup matters for real time.
- Borrow Rust's actionable diagnostics and integrated build/test/doc workflow.
- Avoid copying lifetime complexity and trait-resolution machinery without demonstrated need.

### Zig

See [Zig lessons](zig-lessons.md) for recommendations on explicit allocation and
failure, cleanup, typed errors, compile-time computation, C ABI/targets, and
readability. These are design lessons, not implemented features. Do not copy
unchecked undefined/unreachable into proofs or silently weaken guarantees in
optimized builds.

## 11. Cross-cutting recommendations

The [safety/performance plan](safety-performance.md) records current bottlenecks,
benchmarking requirements, and trust/resource boundaries. No measured performance
baseline or soundness claim follows from that plan.

- Clear errors for quantities, totality, cubical constraints, and inference.
- Bounded implicit search; inspectable search and elaboration results.
- No silent admission of holes; avoid unrestricted implicit conversions.
- Early language server, formatter, incremental checking, stable diagnostic identifiers.
- Explicit ownership/effects/assumptions on FFI boundaries.
- Runtime validation of external values; hardware-model assumptions remain visible.
- Version language, core/artifacts, package formats; record target/backend/foundation/compiler settings.
- Lockfiles, reproducible builds, deprecation/migration policy.
- Avoid unrestricted package build scripts initially.
- Differential backend tests and allocation/stack reports.
- Do not promise stable binary compatibility before representations stabilize.

## 12. Suggested development sequence (not yet a committed schedule)

1. Short specification and tiny executable kernel developed together.
2. De Morgan paths/transport/univalence computation example.
3. Quantitative checking validated with meaningful linear examples; quantities considered from step 1.
4. Idris-like elaboration, holes, diagnostics, basic inductives and matching.
5. Same pure program through C and JS, checked against reference evaluation.
6. Partiality boundary, platform effects, resource/FFI APIs.
7. No-heap Cortex-M program, then target-qualified timing evidence.
8. ESP32 integration; expanded proof tooling and higher inductive types.

No implementation, compiler correctness proof, consistency proof, or hard-real-time certification is claimed by this record.

## 13. Tooling and editor integration

### Decisions

- **Neovim first; VS Code later**, architecturally prepared through a shared protocol. This supersedes the earlier VS Code-first recommendation.
- Shared compiler service and language server; no editor-specific checking logic.
- Standard LSP for diagnostics, completion, hover, navigation, and rename; documented extensions for proof-specific interactions.
- Thin Neovim Lua integration for goals, holes, case splitting, and proof-context views. A later VS Code client consumes the same services.

### Recommended initial scope

- Syntax highlighting, indentation, diagnostics, type-on-hover, hole goals, local context, remaining linear uses, case splitting, suggested edits, and build/test integration.
- CLI commands: check, build, run, test, repl, fmt, doc (illustrative names).
- Incremental checking, cancellation, stale-result handling, machine-readable diagnostics, and stable diagnostic identifiers.
- Cache keys include foundation/version, target, compiler options, and dependencies.
- Progressive disclosure of path boundaries, face constraints, erasure, allocation requirements, backend capabilities, totality, and unsafe/axiom dependencies.
- Embedded cross-compilation, flashing/debugging integration, allocation/stack reports, and timing-evidence status. Estimates must not be presented as guarantees.
- C source mappings for GDB/LLDB; JavaScript source maps; elaboration and normalization traces for checking failures.

First proposed editor milestone: a Neovim hole view showing the goal, local variables, quantities, and checking errors. Tooling is developed alongside elaboration, not postponed until compiler completion.

## 14. Language and specification extensions

Recommendations from the discussion; detailed APIs and syntax are not yet fixed.

- Maintain versioned specifications for core semantics, surface elaboration, platform profiles, and tooling/package protocols. Implementation behavior alone is not the specification.
- Extension proposals state dependencies, compatibility, syntax, typing/computation rules, erasure/totality/trust effects, target requirements, examples, and conformance tests.
- Prefer ordinary libraries first, then notation/elaboration support; require justification for core changes.
- Classify extensions by authority:
  - Libraries: ordinary checked code.
  - Surface notation/macros: expansion into existing checked core.
  - Tactics/deriving/elaboration: produce kernel-checked terms.
  - Backend/platform features: explicit capabilities and trust obligations.
  - Logical primitives/rules: explicit versioned foundation changes and full rechecking.
- Plugins cannot silently change proof validity. Kernel checking does not establish that a generated program matches user intent.
- Explicit project-level experimental opt-ins; possible module-local syntax opt-ins must not change logical foundations.
- Artifacts record language edition, foundation/version, enabled features, plugin versions, backend, and target profile.
- Start with declarative notation and limited checked hooks; delay a general plugin API.
- Restrict plugin filesystem/network authority, support cancellation/execution limits, and make inputs deterministic. Installation must not silently execute packages.
- Do not execute untrusted plugins with unrestricted kernel-internal access.
- RFC lifecycle: proposal, experiment, review, then stabilization, revision, or rejection.
- Review interactions with cubical rules, quantities/borrowing, totality, C/JS semantics, allocation/embedded constraints, and IDE diagnostics.
- Prefer coordinated editions and migrations over an enduring maze of incompatible flags.
- Foundation extensions are project-wide versioned implementations, not per-module kernel patches.

## 15. Documentation strategy

The design record is not the user manual. Develop documentation alongside implementation, with distinct tracks:

| Track | Scope |
| --- | --- |
| Getting started | Installation, first program, REPL, Neovim setup |
| Language tutorial | Idris-like programming, dependent types, quantities, unified proofs/programs |
| HoTT guide | Paths, transport, composition, univalence, higher inductive types |
| Language reference | Precise syntax and language behavior |
| Platform guides | Native C, JavaScript/web, predictable bare metal, hard real-time |
| Library reference | Generated API documentation and examples |
| Contributor guide | Architecture, kernel, elaboration, backends, tests, contribution workflow |
| Specification and RFCs | Formal rules, design decisions, extension proposals and their status |

### Documentation requirements

- Check executable examples in CI, including expected-failure examples. Label illustrative syntax that cannot yet be checked.
- Version documentation with language releases and preserve access to older versions.
- Clearly distinguish implemented, experimental, and planned features.
- State guarantees, limitations, assumptions, and trust boundaries, particularly for logical safety, FFI, memory management, and timing claims.
- Connect editor hovers and library reference pages to the same documentation source.
- Provide an Idris 2 migration guide without requiring prior Idris knowledge for introductory material.
- Keep tutorials approachable and task-oriented; place formal rules in the specification and cross-link them.
- Develop and review documentation alongside code, rather than after implementation.

### First documentation deliverables

1. Documentation index linking these tracks.
2. Fibril guarantees and non-guarantees: totality, partiality, safety, erasure, linearity, platform capabilities, and real-time evidence.
3. Contributor architecture overview explaining module boundaries and trust boundaries.

These are planned deliverables, not a claim that the manuals, generated reference, CI checks, or documentation tooling already exist.

## 16. Unicode source direction

See [Unicode source policy](unicode-source.md). UTF-8 files, Unicode identifiers,
optional mathematical aliases with ASCII alternatives, and Neovim input helpers
are intended. Strict UTF-8 decoding, bounded raw-file loading, and decoded-text
validation are implemented separately. Identifier tables/normalization,
confusable diagnostics, and aliases are not.
Never globally rewrite strings or silently normalize full source. Position
encodings must be explicit at file/editor boundaries.

## 17. Lightweight package-management direction

Future user projects use a pubspec-style fibril.yaml plus fibril.lock. Keep pack
for the Idris implementation. Start with local packages, then pinned Git sources,
shared caches, and offline/reproducible builds; defer registries/advanced solving.
No automatic dependency scripts. See [package design](packages.md) for the proposed
schema, YAML restrictions, target conditions, and unresolved identity/lock rules.
This is not implemented yet.

## 18. Readiness and immediate open design work

- Write precise guarantees/non-guarantees for total, safe, erased, linear, and real-time.
- Select the published De Morgan calculus and formalize quantitative interactions.
- Define partiality and unsafe-dependency rules.
- Design scoped borrowing for linear buffers/peripherals without escaping references.
- Choose hosted memory management and embedded storage interfaces.
- Select first Cortex-M and ESP32 boards and concrete timing requirements.
