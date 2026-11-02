# 8. What comes next—and what not to assume

## Learning goals

Understand how current pieces fit a future language without mistaking a roadmap
for an implemented compiler.

![Intended pipeline](../diagrams/roadmap.svg)

Dashed stages are future work. The erased checker is a partial ordinary
prototype, not the intended complete checker.

## The next foundational gap

Our ordinary quantities and cubical algebras currently coexist without combined
term rules. Composition, overlapping boundaries, transport, and Glue need a
resource policy with substitution and reduction arguments. We must not implement
a plausible-looking combination and inherit soundness by citation.

## Surface language and tooling

Explicit nonrecursive declaration files now lower to typed lets with a main
entry; their earlier values are opaque during later checking. Named modules now
provide transparent closed erased/unrestricted globals and checked direct imports.
Recursive declarations/modules remain future work.

A separate declaration elaborator now lowers explicit records, constructors,
eliminators and safe projections into independently checked code. Typed consuming
patterns are supported. Implicit argument/interface elaboration and tactics remain
future work; any generator or derivation tool must still produce checked terms.

The first [Neovim/Vim lexical runtime](../editor-highlighting.md) now supplies
syntax colors and file detection, saved-snapshot checking/navigation, conservative
project definition lookup, references/rename previews and manual unsaved-buffer
formatting. Lexical coloring remains distinct from semantic checking.

Neovim comes first for the future shared compiler service and language server.
VS Code should reuse that protocol later. Editor interaction must not introduce
its own checking logic or silently accept unfinished goals.

## Compilation and platforms

A future erasure/runtime IR should feed C and JavaScript. They need consistent
observable semantics. Computationally relevant transport cannot be discarded
simply because it looks like a proof.

Embedded profiles target Cortex-M and selected ESP32 variants. Predictable
bare-metal execution is not a verified deadline guarantee; hard-real-time claims
require target/application-specific timing evidence.

## Lightweight project management

The [package plan](../packages.md) uses fibril.yaml and fibril.lock for future
user projects, inspired by Dart pub. Local packages come first; pack still builds
the Idris implementation. Manifest parsing/resolution does not exist yet.

## Extensibility and self-hosting

Foundation choice is project-wide; switching requires rechecking. Plugins may
assist term construction, not patch proof validity per module.

Self-hosting follows a sufficiently practical native subset. Keep a reproducible
Idris bootstrap route. A self-hosted compiler is not automatically correct.

## Design discipline

Use the [design record](../design.md) for agreed direction and open questions.
Use the implementation chapters for actual behavior. When they disagree, fix
the documentation rather than silently promoting a proposal into a guarantee.

**Exercise:** name one missing logical feature, one missing tooling feature,
and one platform requirement that cannot be certified from totality alone.

**Further reading:** [guarantees](../guarantees.md), [first milestone](../milestone-01.md),
[pipeline dependency evaluation](../pipelines-evaluation.md).
