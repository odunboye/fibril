# Check and run local packages

## Use cases and status

**Implemented POSIX bootstrap:** put reusable email/domain, HTTP, storage or UI
code in separately owned local packages without importing it into the compiler.
An application declares direct path dependencies, then explicitly imports their
source modules. For a small program, a single source root is simpler and remains
fully supported. This adds project organization and validation, not a new core
language feature, backend or language-level package authority.

~~~sh
fibril check                    # current directory's fibril.yaml
fibril run
fibril module-graph
fibril check --package path/to/fibril.yaml
fibril run --package path/to/fibril.yaml
fibril module-graph --package path/to/fibril.yaml
~~~

Bare check, run and module-graph select only ./fibril.yaml. No parent-directory
search or fallback occurs, including when the local manifest is malformed.
Use --package PATH to select another project's exactly named fibril.yaml;
explicit source operands and --source-dir retain their existing meaning.
check prints the ordinary checking summary; run
reserves stdout for the checked program. Graph inspection is syntax-only JSON,
with checked false and a package_scope containing entry package, sorted package
inventory, canonical source roots, direct dependencies and per-module owners.
It is not a typing certificate or locked snapshot. Package-aware eval, editor
navigation and version-2 project checking reports are not wired up yet.

![Local package loading boundary](diagrams/local-packages.svg)

## Real two-package example

From the compiler project:

~~~sh
./build/exec/fibril check --package examples/packages/mailer/fibril.yaml
./build/exec/fibril run --package examples/packages/mailer/fibril.yaml
~~~

The second command prints accepted by relay: demo-1 (not delivery).
The [mailer manifest](../examples/packages/mailer/fibril.yaml) declares
email-core at ../email-core. Its [Main](../examples/packages/mailer/src/Main.fib)
imports Email.Core.Status and calls a [Fibril-authored linear String
function](../examples/packages/email-core/src/Email/Core/Status.fib) from the
other package. The dependency owns Email.Core; its full source path remains
src/Email/Core/Status.fib, not src/Status.fib. The root application owns Mailer
and selects Main separately.

This is genuine multi-root source checking and hosted IO execution, not a merge
of independently checked graphs, a networked email server, generated C/JS or
proof of mail delivery. The [larger application target](applications/transactional-email.md)
retains its explicit networking/storage/backend blockers.

## Discovery and filesystem admission

[Project.Local](../src/Fibril/Project/Local.idr) loads the entire explicitly
declared **dependency closure**, including manifests whose source modules are
not imported. It does not discover disconnected workspace members. The strict
[manifest profile](manifests.md) is unchanged:

- A dependency path is relative to the declaring package directory, never cwd.
  Append exactly fibril.yaml; no alternative filename or parent search.
- The incoming dependency key must equal the target's declared name on **every
  edge**, even when the canonical manifest is already cached.
- One package name resolving to different canonical manifests is rejected.
  Shared diamonds reuse one canonical manifest while retaining all edges.
- Check exact spelling of every supplied path component, including manifest,
  source directory and module components, on case-insensitive hosts too.
- The supplied terminal filename must be fibril.yaml. Manifest-file symlinks
  cannot redirect it to another canonical filename/directory. Canonical directory
  aliases resolving to the same package are deduplicated; they do not create a
  second package identity.
- Source roots must be existing directories canonically contained in their
  package directory. Equal or nested canonical source roots across distinct
  packages are rejected. Package directory nesting alone is not forbidden when
  source roots remain disjoint. Symlink escapes fail; normal Unicode/spaces remain.
- Admission is incremental: 64 distinct manifests, discovery depth 64 and 256
  declared edges. Each manifest has an 8192-byte pre-read cap. Thus the planner
  never receives an unbounded discovered inventory. The normal pure planner then
  validates names, namespace collisions, foundation consistency and cycles.

These checks use realpath and bounded exact-entry directory scans (4096 entries
per lookup). They do not identify inode/hard-link aliases, pin directory handles,
sandbox a hostile filesystem, detect same-size edits or lock an atomic snapshot.
Host blocking/OOM/crashes remain outside represented-error guarantees. Manifests
are not content-hashed or reread during program execution; no reproducibility or
publisher-authenticity claim is made.

## Source ownership and checking boundaries

[ModuleGraph](../src/Fibril/Driver/ModuleGraph.idr) performs **one traversal**
across roots and retains PackageRoots scope metadata. At each source import:

1. Resolve the globally unique component-prefix owner.
2. Require self or an explicit **direct** package dependency, before path lookup
   or any source-snapshot cache hit. No transitive fallback or root search.
3. Resolve the full module path inside that owner's canonical source root, with
   exact case/header identity checks and canonical containment.
4. Still require the importing source file's explicit module import before
   exported values, interface schemas or implementations become visible.

Main is selected only by the root's explicit entry: Main. Dependency entries
are not substituted, and no library may own/import the reserved Main namespace.
The application's entry file must declare module Main. Other source files must
match their requested owned module name.

The existing graph-wide 32-module, depth-32, 524288-byte aggregate and 65536-byte
per-source-file limits remain shared across every root. Header/import/parser and
200000-node expansion/checking limits are unchanged. Resource admission is not
bounded memory, memory safety or a hard deadline.

Every declaration in every **reachable module**, including private/unused bodies,
is checked through the ordinary elaborator and independent core checks before
its exports are exposed. Unimported source files are not crawled or checked.
Only after the whole graph checks and a complete bounded IO plan is prepared
may run perform host stdout effects. Host output failures may still be partial.
Package plans, graphs and acceptance reports remain public data, not certificates.

## Evidence and next work

CLI regressions cover a real two-/three-package graph, dependency-relative paths
from other working directories, direct/transitive permission after cache hits,
shared diamonds, unimported bindings, invalid private bodies with no stdout,
malformed unimported dependency manifests, cycles, missing/wrong-case paths,
source-root escapes/nesting and both same-directory/relocating manifest aliases.
Admission tests exercise 64/65 packages, 256/257 edges, oversized manifests,
32/33 modules and exact/one-over aggregate source-byte budgets across roots.
The ordinary single-root suite is retained.

[Namespace-aware scaffolding](project-creation.md) emits a manifest by default
with namespace App; --module-prefix PREFIX overrides it and --source-only opts out. Next: workspace-member inventory
files, package-aware editor/report services and a separately specified source
snapshot/hash lock contract. No network fetching, registry/version solving,
hooks, build scripts, native bindings or implicit plugin discovery are added.
