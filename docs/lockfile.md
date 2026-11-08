# Design: fibril.lock (local snapshot locks)

Status: **design only, nothing here is implemented.** It narrows the open
"lock format/versioning" items in [packages.md](packages.md) and
[workspaces.md](workspaces.md) to the smallest slice that is honest today.

## Use case

Detect when a local path dependency changed since the last reviewed build, so a
project build is reproducible and a silent edit to `../email-core` is visible.
This is **change detection, not pinning**: path dependencies stay mutable, and
a hash proves nothing about who wrote the content.

## Non-goals

Registry, Git sources, version constraints, a solver, signatures, remote fetch,
and per-target conditions. Those need their own designs
([packages.md](packages.md) sequence steps 3 and 4).

## File

`fibril.lock` sits beside the root `fibril.yaml`. It is machine-written and
**JSON** (reusing [Driver.JSON](../src/Fibril/Driver/JSON.idr) escaping), not
YAML, so the strict YAML profile need not grow a writer and diffs stay stable
through sorted keys and two-space indentation.

```json
{
  "schema": 1,
  "root": "mailer-app",
  "foundation": "de-morgan",
  "packages": [
    {
      "name": "email-core",
      "module-prefix": "Email",
      "path": "../email-core",
      "manifest-sha256": "…64 hex…",
      "tree-sha256": "…64 hex…"
    }
  ]
}
```

- `packages` lists the root and every package in its dependency closure, sorted by
  `name`. Names are already unique identities in the version-one contract.
- `path` is relative to the root manifest's directory and informational: identity
  is `name` plus digests, never the path alone.
- `manifest-sha256` hashes the exact bytes of that package's `fibril.yaml`.
- `tree-sha256` hashes its source tree: for each `*.fib` file under `source-dir`,
  sorted by path bytes, take the line `<relative path>\0<file sha256 hex>\n`, and
  hash the concatenation. Paths are `/`-separated and relative to `source-dir`.
  Other files (build output, editor state) are ignored.
- The compiler build is **not** locked. It belongs in the build cache key
  ([packages.md](packages.md#reproducibility-and-trust)). `foundation` is locked
  because a change requires rechecking.

## Behavior

| Command | Lock absent | Lock present |
| --- | --- | --- |
| `fibril lock` | writes it | refuses; use `--update` |
| `fibril lock --update` | writes it | rewrites it, printing each changed package |
| `fibril check` / `run` / `test` with `--package` | proceeds, prints `no fibril.lock` | verifies; any mismatch is an error naming the package and which digest differs |
| same, with `--locked` | error | as above |

Verification runs before any dependency source is checked, so a drifted package
is never half-trusted. A package present in the closure but absent from the lock
(or the reverse) is a mismatch, not a warning. The command never fetches, runs
scripts, or rewrites the lock implicitly.

## Open questions

1. **SHA-256 in Idris.** [workspaces.md](workspaces.md) requires "maintained
   SHA-256 support". None is pinned in `pack.toml` yet. Candidates are a pack
   collection library, or a small FFI to the native runtime already linked in
   `runtime/native`. This is the main blocker and needs a decision before code.
2. **Line endings.** Hash raw bytes (a CRLF checkout changes the digest, which
   is strict but surprising) or normalize. Recommendation: raw bytes, documented.
3. **Symlinks.** Recommendation: reject a symlink inside `source-dir`, matching
   the loader's canonical-path checks in [local-packages.md](local-packages.md).

## Implementation slices

1. Pure `Project.Lock` module: tree digest and lock encode/decode, with tests on
   fixed inputs (ordering, empty tree, CRLF, non-ASCII path, duplicate name).
2. SHA-256 per open question 1, checked against published test vectors.
3. `fibril lock` plus verification inside the existing `--package` closure loader.
4. CLI tests in `tools/test_cli.py`: edit a dependency file and expect a named
   mismatch; add/remove a package; `--locked` without a lock.

Each slice is testable offline. Slice 1 needs no digest implementation if tests
inject a stub hash function.
