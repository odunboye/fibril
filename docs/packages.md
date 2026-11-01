# Lightweight Fibril project and dependency management

Status: agreed direction; not an implemented manifest reader or package resolver.

## Bootstrap versus user projects

- pack.toml and Idris .ipkg files continue to manage the compiler implementation.
- Future Fibril projects use a small pubspec-style **fibril.yaml** manifest and
  **fibril.lock** lockfile.
- Borrow Dart pub's readable project description and integrated workflow, not its
  complete registry/version-solving machinery.
- This does not replace the existing pack setup or add a dependency today.

## Proposed manifest

Illustrative only; the exact schema/version rules are still to be specified:

```yaml
name: hello_fibril
version: 0.1.0

environment:
  fibril: ">=0.1.0 <0.2.0"

foundation: de-morgan

dependencies:
  collections:
    path: ../collections
  browser:
    git:
      url: https://example.org/browser.git
      rev: "<full-commit-hash>"
```

This example is not a runnable dependency configuration. Target-specific
dependencies also need an explicit schema, so browser packages do not contaminate
an unrelated embedded build.

The first [local module/import contract](modules.md) precedes package resolution:
one explicit source root, checked qualified exports, an acyclic graph, and no
network or manifest reader. Its design is not implemented module loading yet.

## Minimal implementation sequence

1. Local-path packages and a deterministic module/dependency graph.
2. Explicitly pinned Git dependencies with a shared content cache.
3. Lockfile verification, offline builds from cached inputs, and update commands.
4. Registry and version resolution only when justified by actual use.

Initially select one revision per package identity and report conflicts clearly.
Do not invent a sophisticated solver before a registry exists.

Proposed commands: fibril deps, check, build, test, run. Only current commands in
the [CLI guide](cli.md) exist; these names are a roadmap.

## Reproducibility and trust

- The manifest describes intent; the lockfile records resolved immutable revisions
  and content hashes. Commit lockfiles for reproducible project builds.
- Path dependencies are mutable: record/verify content for a snapshot, or mark
  builds dirty and require explicit updates. A path name alone is not a pin.
- Specify package identity and source-conflict rules; names alone are insufficient.
- Resolve and verify revisions/hashes before using cached contents.
- Build cache keys include compiler, foundation/version, backend, target, options,
  and dependency content. A foundation change requires rechecking.
- Separate fetch/resolve from build and support offline operation once cached.
- No automatic dependency build scripts, install hooks, or plugin execution.
- Hashes detect changed content; they do not establish publisher authenticity.
  Future registry/signature/authentication policy needs separate design.
- Reject dependency cycles unless a deliberate module system later justifies them.

## Keep YAML predictable

Use a maintained parser, not an ad-hoc YAML implementation. Accept a documented
small schema/profile; reject duplicate keys, unknown fields, custom tags, aliases,
and implicit scalar surprises. Require quoted compiler constraints/revisions where
ambiguity exists. Pin the parser/profile and bound input size and expansion work.

No YAML library has been selected. Manifest parsing, lock format/versioning,
workspace behavior, target conditions, and compatibility policy remain open.

## References

- [Dart pubspec](https://dart.dev/tools/pub/pubspec)
- [Dart dependency sources](https://dart.dev/tools/pub/dependencies)

These are workflow inspiration, not promises of Dart format compatibility.
