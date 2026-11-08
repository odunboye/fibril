# Lightweight Fibril project and dependency management

Status: [offline console scaffolding](project-creation.md) is implemented.
[Pure workspace planning and direct-dependency routing](workspaces.md) are implemented
as internal APIs. [Strict local manifest inspection](manifests.md) is implemented;
[explicit local dependency-closure check/run](local-packages.md) now works too.
[Local snapshot locks](lockfile.md) are implemented. Workspace-member discovery,
fetching, registries and version solving remain unimplemented.

## Bootstrap versus user projects

- pack.toml and Idris .ipkg files continue to manage the compiler implementation.
- Local Fibril projects use a small pubspec-style **fibril.yaml** manifest;
  a **fibril.lock** snapshot/hash lockfile is [implemented](lockfile.md) for local
  paths only.
- Borrow Dart pub's readable project description and integrated workflow, not its
  complete registry/version-solving machinery.
- This does not replace the existing pack setup. The bootstrap now uses the
  collection-pinned yaml library for strict inspection, not application fetching.

## Local-only version-one contract

The [workspace contract](workspaces.md) now defines explicit package names,
owned module prefixes, source roots, direct dependencies and separate entry
selection. The schema is local-only and can now be inspected with fibril manifest PATH:

~~~yaml
schema: 1
name: mailer-app
module-prefix: Mailer
source-dir: src
foundation: de-morgan
entry: Main

dependencies:
  email-core:
    path: ../email-core
~~~

Bare check/run/module-graph select ./fibril.yaml only; --package PATH selects
another project explicitly. There is no parent-directory search. The initial schema deliberately excludes
Git/registry sources, target conditions, native hooks and version solving. Those
must get explicit later contracts rather than silently accepted fields. Package
names do not infer namespaces or grant source-level visibility.

The first [local module/import contract](modules.md) precedes package resolution:
one explicit source root, checked qualified exports, an acyclic graph, and no
network or parent-directory manifest search. Syntax/discovery and imported checking are implemented; package resolution
now supports explicit local paths through --package; remote resolution remains future work.

## Tooling boundary and first scaffold

Use one user-facing fibril CLI, but keep project/dependency tooling separate from
the trusted compiler and reusable through stable services. The first project
module has no checker/parser imports; runtime filesystem operations are explicit.
A separate executable/package may host these tools later without making users
learn unrelated command names. Do not automatically execute PATH-discovered
plugins or template hooks.

fibril new NAME [--template console] [--module-prefix PREFIX | --source-only] [--dry-run] creates
a source tree, README, gitignore and working local fibril.yaml with namespace App.
--module-prefix overrides the default; --source-only omits the manifest.
No lockfile is emitted. init into existing directories,
workspace-member inventories, fetching and remote templates remain future slices.

## Minimal implementation sequence

1. Local-path packages and a deterministic module/dependency graph (explicit closure implemented).
2. Namespace-aware scaffolds (implemented), then workspace-member inventories and versioned snapshot locks.
3. Explicit pinned Git dependencies/cache only with separate fetch/offline verification policy.
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

The [strict reader](manifests.md) selects collection-pinned idris2-yaml, validates
events before composition and rejects unsupported YAML/schema features. Filesystem
workspace-member discovery and lock format/versioning remain pending; the
[local workspace ownership/order contract](workspaces.md) is specified and tested. Target conditions and compatibility/version-selection
policies need separate later schema work.

## References

- [Dart pubspec](https://dart.dev/tools/pub/pubspec)
- [Dart dependency sources](https://dart.dev/tools/pub/dependencies)

These are workflow inspiration, not promises of Dart format compatibility.
