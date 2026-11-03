# Local package and workspace contract

## Use cases and status

Use packages to develop email, HTTP, storage, browser/mobile adapters and UI
libraries independently of the compiler. A workspace lets those packages evolve
in one checkout without turning them into compiler-internal modules. Prefer an
ordinary module tree for a small program with no reusable package boundary.

**Implemented now:** a pure local inventory planner in
[Project.Workspace](../src/Fibril/Project/Workspace.idr), with ordering, namespace
ownership and direct-dependency checks. It has no filesystem effects or compiler
imports. This is not a manifest reader, workspace-aware check/run command, package
fetcher or lockfile implementation. The current explicit single-root CLI remains
unchanged; fibril new still emits no manifest.

![Workspace planning boundary](diagrams/workspaces.svg)

## Three distinct identities

- A directory slug is a scaffolding input, such as mailer-app.
- A package name is a version-one local inventory key. Its deliberately chosen
  profile is the same 1..64 lowercase ASCII letters/digits/_/- spelling, starting
  with a letter. Project.Name exposes separate project/package validators.
- A module prefix is explicit, such as Mailer or Email.Core. It is never inferred
  from a package name or directory, and carries no special compiler privilege.

Every package owns one nonempty component prefix in this first contract. Prefix
components use the existing capitalized ASCII module-component profile, with at
most sixteen components. Prefix ownership is component-based: Text conflicts
with Text.Greeting, not Textual. Sibling Text.Left/Text.Right owners are disjoint.
Duplicate and ancestor/descendant owners reject rather than selecting a longest
match. Additional prefixes per package are deferred, not silently merged.

Main is reserved as a library namespace root in this workspace contract. Each
application entry is selected separately; dependencies do not export a shared
Main, and imported main is never substituted for the application's own entry.
This policy does not change today's single-root module rules.

## Implemented planner input and output

A PackageSpec contains its explicit name, supplied source-root string, owned
module-prefix components, foundation string and direct dependency names.
For example, this is host Idris, not source-language package syntax:

~~~idris
core = LocalPackage "core" "/workspace/core/src" ["Core"] "de-morgan" []
mail = LocalPackage "mail" "/workspace/mail/src" ["Mail"] "de-morgan" ["core"]
app  = LocalPackage "app" "/workspace/app/src" ["App"] "de-morgan" ["mail"]
~~~

planWorkspace [app, mail, core] returns order [core, mail, app]. When several
packages are ready, the lexicographically smallest name wins. Reordering the
inventory or direct dependency lists does not change that order. The output
inventory is also sorted by name; direct edges are not replaced by a closure.
Dependency-list spelling/order is retained, so this is not canonical serialized
plan output. Validation reports the first encountered error, not a promised
canonical diagnostic under malformed-input permutations.

The planner validates all supplied members, including disconnected packages:

- Nonempty inventory, valid names/prefixes and nonempty source-root strings.
- No duplicate package name or equal supplied root string.
- No namespace overlap, missing/repeated/self dependency or dependency cycle.
- Exactly the currently supported de-morgan foundation metadata.
- Explicit admission: defaults are 64 packages and 256 direct edges; the API
  accepts a caller-supplied WorkspaceLimits profile. These are work limits, not
  semantic language maxima, source-byte limits or memory/time guarantees.

A cycle error lists blocked packages, which can include dependents; it does not
pretend every listed package is itself on the cycle. No partial successful plan
is returned.

## Two separate import boundaries

moduleOwner plan requester components finds the unique owner and then permits
only self or a declared **direct** package dependency. Unknown requesters,
unknown/ambiguous ownership and malformed module vectors fail closed. It does
not search only authorized roots and fall back to another root.

With app -> mail -> core:

- app may route App.MainView and Mail.Queue.
- mail may route Core.Text.
- app may not route Core.Text unless app also declares core directly.

Package permission is only the first boundary. A source file must still directly
import the particular module before it can use its exported declarations,
interface schemas or implementation providers. Private declarations and unused
bodies retain ordinary checking rules. Workspace planning is not source coverage,
module cycle checking or a typing certificate.

Do not concatenate separately loaded ModuleGraph values or fabricate checked
module snapshots from this package DAG. A real multi-root loader needs explicit
per-module ownership and must preserve module-level admission and checking.

## Filesystem adapter contract (not implemented)

Source roots in the pure API are ordinary untrusted strings. Equality checks do
not prove that paths exist, are canonical, identify directories, remain stable or
are disjoint. Spaces/Unicode are preserved, not trimmed or case-folded. Different
spellings such as /a/../b and /b are not resolved by the planner.

The future adapter must canonicalize package/source roots before loading,
validate exact case and containment, reject source-root aliasing/nesting in the
initial profile, and reject canonical-file aliases across owners. Canonicalization
is not an atomic snapshot or hostile-filesystem sandbox.

Keep the existing module-to-file mapping: Email.Address maps to
SOURCE_ROOT/Email/Address.fib, not SOURCE_ROOT/Address.fib. Ownership does not
strip prefixes. Entry Main can remain SOURCE_ROOT/Main.fib when explicitly
selected by the root application; it does not become a library import route.

Package paths are resolved relative to the depending manifest's directory, not
the shell's current directory. Explicit local dependencies may point outside the
workspace through a declared relative path. source-dir must resolve inside its
package directory; source symlinks escaping that boundary are rejected. No path
source implies permission to execute scripts or fetch remote content.

## Version-one logical manifest schema (reader pending)

The intended fibril.yaml schema is deliberately local-only:

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

Required fields: schema, name, module-prefix, source-dir, foundation. entry is
optional; the initial reader profile accepts Main only, selecting SOURCE_ROOT/Main.fib
separately from the library namespace. General entry-path/module overrides need
a later mapping contract. This does not restrict today's explicit single-root CLI.
Absent dependencies means none. A dependency mapping key must equal the target
manifest's declared package name; aliases and implicit namespace renaming are
not supported. Paths are explicit local paths; registry/Git/native/plugin/script
fields are unsupported, not ignored.

A future fibril.workspace.yaml lists schema: 1 and explicit relative members.
There is no automatic parent-directory search, filesystem crawling for members,
implicit dependency on every member, or global package cache lookup. A package
name selects only the explicitly declared target. One name/prefix owner wins by
validation, never by path-search order. No version solver or side-by-side version
selection is included.

These are integration contracts, **not executable configuration yet**. Select a
maintained YAML parser/profile before implementing the reader. Reject duplicate
and unknown keys, aliases/tags, schema mismatches, implicit scalar surprises,
unsupported dependency sources and resource exhaustion. Do not hand-roll a YAML
parser or accept fields with no implemented meaning.

## Reproducibility, foundation and foreign trust

Names and paths alone are not immutable package identity. Before claiming locked
builds, define/version the lock format, select maintained SHA-256 support and
record canonical dependency identity, exact source content and the compiler/
foundation/target/runtime profile. Local changes must be visible as dirty inputs
or require an explicit update policy. Nothing in this planner verifies a lock or
content digest, selects language versions or establishes publisher authenticity.

Only de-morgan metadata is currently admitted. This is consistency checking,
not a foundation switch in the compiler or evidence of quantitative/cubical
soundness. A package cannot patch checking rules or inherit validity from its
manifest. Foreign/native bindings remain explicit trust assumptions requiring
runtime input validation and target/ABI policies in a later schema.

Never run install/build hooks during discovery or checking. Future remote
fetching must be an explicit operation and stay separate from offline builds.
The first local loader should need no registry or network connection.

## Evidence and next slices

[Tests.Workspace](../test/src/Tests/Workspace.idr) covers ordering/permutation,
independent members, identity/root/profile failures, component-prefix distinctions,
dependency conflicts/cycles, foundation metadata, admission limits, direct versus
transitive routing, unknown requesters, forged ambiguity and Main separation.
Root tests deliberately use nonexistent paths: no filesystem validation is claimed.
Read-only parallel review supplied the module-loader integration constraints.

Next: maintained manifest decoding -> canonical local-root resolution -> real
workspace-aware module loading/reporting/navigation -> source snapshot locking.
Keep all present single-root commands compatible until that path is tested end to
end. Project scaffolding can emit manifests only when the reader really works.
