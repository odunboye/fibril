# Contributing to Fibril

Start with [architecture](docs/architecture.md), [core proposal](docs/core-draft.md),
and [foundation baseline](docs/foundation-baseline.md).

Use the collection pinned in `pack.toml`; avoid unrelated toolchain upgrades.

## Definition of done

- Focused implementation with documented invariants and no hidden trust expansion.
- Public API and module documentation following the
  [documentation policy](docs/documentation-policy.md).
- Positive and negative tests where appropriate, plus structural properties
  where useful; see the [testing guide](docs/testing.md).
- Preserve Hedgehog failure seeds and promote counterexamples to regressions.
- Updated design/reference/example material for changed behavior.
- Passing `make test`, `make examples`, and `make docs`.
- A meaningful commit containing code, tests, and related documentation.

No unchecked holes or unsafe axioms should be introduced as completed proofs.
Experimental rules must be labeled and separated from established guarantees.
Keep generated build/API artifacts out of commits.
