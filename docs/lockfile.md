# fibril.lock (local snapshot locks)

Status: **implemented** for local path packages (POSIX bootstrap): `fibril lock
[--update] [--package PATH]` writes it and every package command that loads the
dependency closure (`check`, `run`, `test`, `module-graph`, `emit-c` and editor
navigation through `--package`) verifies it first. Not implemented: the
`--locked` flag, a "no lock" notice, workspace members, and anything remote. It
narrows the open "lock format/versioning" items in [packages.md](packages.md) and
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
YAML, so the strict YAML profile need not grow a writer. Output is canonical: fixed key order,
packages sorted by name, one package object per line (so diffs are per package),
trailing newline. `Fibril.Project.Lock.encodeLock` implements exactly this.

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
| any package command (bare or `--package`) | proceeds silently, unchanged | verifies; any mismatch is an error naming the package and which digest differs |
| same, with `--locked` | error | as above (**not implemented**; a missing lock is silently accepted) |

`fibril lock --update` with an unreadable or non-canonical lock replaces it and
says so. The lock is written to `fibril.lock.tmp` and renamed into place. A
symlink or alias anywhere in a package's source tree, or more than 2048 files, 16
levels or 4096 entries per directory, makes locking and verification fail.

Verification runs before any dependency source is checked, so a drifted package
is never half-trusted. A package present in the closure but absent from the lock
(or the reverse) is a mismatch, not a warning. The command never fetches, runs
scripts, or rewrites the lock implicitly.

## Open questions

1. **SHA-256 in Idris. Resolved.** `Fibril.Project.Digest.sha256Hex` wraps the
   collection-pinned `sha` package (C implementation, installed by `pack`; its
   build hook only compiles two C files, but `pack` asks for confirmation).
   Checked against the FIPS 180-4 vectors in `Tests.Digest`. It takes a
   `List Bits8`, so large inputs are slow; fine for source files.
2. **Line endings.** Hash raw bytes (a CRLF checkout changes the digest, which
   is strict but surprising) or normalize. Recommendation: raw bytes, documented.
3. **Symlinks.** Recommendation: reject a symlink inside `source-dir`, matching
   the loader's canonical-path checks in [local-packages.md](local-packages.md).

## Implementation slices

1. **Done (encode and drift only):** pure `Fibril.Project.Lock` with `treeDigest`
   (rejects empty, absolute, `.`/`..`, NUL and duplicate paths), `encodeLock` and
   `lockDrift`. Tested against digests computed independently with Python
   hashlib.
2. **Done:** SHA-256 per open question 1, checked against published vectors.
3. **Done:** `Fibril.Project.LockDecode.decodeLock`, a strict reader. It parses
   only the exact layout `encodeLock` writes (digests must be 64 lowercase hex,
   names unique) and then requires re-encoding to equal the input, so unknown or
   duplicate keys, reordering, whitespace, other schemas and trailing data are
   all rejected. A hand-edited lock must be regenerated with `fibril lock --update`.
4. **Done:** `fibril lock` and verification inside `Project.Local.loadLocalInventory`
   (reads files, rejects symlinks, builds the current `Lock`, calls `lockDrift`).
5. **Done:** CLI tests (`LockfileTests` in `tools/test_cli.py`); the digests were
   also cross-checked against an independent Python implementation. Original plan:
   `tools/test_cli.py`: edit a dependency file and expect a named
   mismatch; add/remove a package; `--locked` without a lock.

Each slice is testable offline. Slice 1 needs no digest implementation if tests
inject a stub hash function.
