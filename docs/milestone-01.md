# Milestone 01: explicit core checking

Status: planned; only quantity representation and a CLI skeleton exist.

## Foundation gate

Before implementing cubical typing rules:

1. Select and cite a specific published De Morgan calculus.
2. Specify universes, interval/face contexts, conversion, and path rules.
3. Write the proposed quantitative interaction rules, with counterexamples and
   explicit unresolved obligations. Do not claim consistency from feature reuse.
4. Define how partial and unsafe dependencies are excluded from trusted proofs.

## Scope

A small explicitly typed core, reference evaluation, structured checking errors,
and tests. No full surface elaborator, plugin API, C/JS backend, or timing claims.

## Acceptance criteria

- Check and evaluate dependent identity functions and applications.
- Accept and reject representative erased, linear, and unrestricted uses.
- Reject reuse or discarding of a linear value where the selected rules require it.
- Check path boundaries and evaluate endpoint applications.
- Demonstrate transport computation in the selected cubical fragment.
- Reject partial definitions in trusted proof dependencies.
- Report unsupported syntax/features rather than silently admitting them.

Computational univalence is a subsequent explicit milestone if the initial
fragment does not yet include composition and Glue.

## Later milestones

Idris-like elaboration and Neovim LSP; C/JS semantic parity; no-heap Cortex-M;
target-specific timing evidence; ESP32; incremental self-hosting.

Self-hosting starts after a practical native subset can implement compiler data
structures, IO, modules, and checking. Idris 2 remains the reproducible bootstrap
and reference implementation during migration. Self-hosting is not a soundness proof.
