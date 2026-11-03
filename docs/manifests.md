# Strict local package manifest inspection

## Use cases and status

**Implemented:** validate a local fibril.yaml and inspect its explicit package
metadata before adding filesystem resolution. This catches configuration typos,
unsupported fields and unsafe YAML features without traversing dependency paths
or executing a program. Prefer the existing explicit-source-root commands for
checking/running source; inspection is not package installation or compilation.

~~~sh
fibril manifest path/to/fibril.yaml
~~~

The command returns JSON with version 1, kind manifest-inspection and
checked/resolved/locked all false. It reports validated schema values, not
canonical filesystem roots, resolved dependencies, source acceptance or a lock.
This adds configuration validation/convenience, not language expressiveness.
Errors go to stderr and return nonzero; no files are written. No auto-discovery,
network connection, hooks, plugins or shell expansion occurs.

![Strict YAML decoding boundary](diagrams/manifests.svg)

## Version-one package schema

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

Required: schema, name, module-prefix, source-dir and foundation. Optional entry
accepts Main only, separate from the library namespace. Optional modules is a
sequence of unique owned module names; optional tests selects one owned Bool
suite module, while mutually exclusive test-package selects a separate contained
local test package directory. Root libraries need a nonempty inventory for check/test; see
[libraries and tests](libraries-and-tests.md). Absent dependencies or
an empty mapping means none. Every dependency has a valid non-self package-name
key and exactly one path field. Registry/Git/version/native/build-script fields
are rejected, not ignored. Target-manifest name equality is enforced by the separate local loader.

The [workspace contract](workspaces.md) defines name/prefix ownership semantics.
Package names use the explicit lowercase ASCII slug profile. Prefixes use up to
sixteen capitalized ASCII components and cannot own Main or its descendants.
Only de-morgan foundation metadata is supported; this does not switch the kernel.

String-valued fields must be YAML strings. Unquoted true, null, numbers and empty
values do not become strings accidentally. schema must be exactly the plain
integer spelling 1, not quoted "1", +1, 0x1, a float or a boolean. Normal comments,
plain/single/double quoting, single-document markers and flow mappings are accepted
where they fit the schema. Block/multiline scalars remain forbidden. Sequences
are accepted only as the flat modules inventory; other sequence fields reject.

source-dir is a nonempty relative path with no empty, dot or parent components.
Dependency paths may explicitly use parent/dot components such as ../email-core
or ., but may not be absolute. Both reject backslashes, colons and decoded
controls, preserving normal spaces/Unicode without trimming or normalization.
This portable lexical profile is not containment, symlink or path-existence
validation. Tilde/environment variables have no expansion semantics here.

[The two inspection fixtures](../examples/manifests/README.md) deliberately have
no src directories. Both inspect successfully. A unit test passes their decoded
shape into the pure planner with synthetic roots. The separate
[local package workflow](local-packages.md) supplies a real two-package check/run
example; inspection itself remains read-only schema decoding.

## Maintained parser and strict composition

The bootstrap now depends on idris2-yaml from the existing pinned
nightly-260903 collection: revision d946ee063cad5367f30630b357e142713ee04495,
[BSD-2-Clause notice](assets/licenses/idris2-yaml.txt), with its parser dependencies managed by pack. This is a pure Idris
YAML 1.2.2 parser, not handwritten parsing in Fibril or a libyaml C adapter.
The compiler kernel does not import it or derive typing validity from it.
Bootstrap dependency installation and application dependency fetching remain
separate; inspecting a manifest does not run pack or fetch anything.

The boundary in [Project.Manifest](../src/Fibril/Project/Manifest.idr) is:

1. Apply input admission and conservative directive rejection.
2. Call the maintained parseEvents API.
3. Reject every anchor, alias and explicit tag, including standard tags and !.
   Reject block/multiline scalars, excessive collection depth/event count and
   multiple documents **before composing**, so aliases are never expanded.
4. Call composeWith Core, which supplies duplicate-key detection, including
   quoted/escaped-equivalent string keys.
5. Decode only known scalar/mapping shapes, the flat modules sequence and the strict field types above.

YAML directives do not survive in the library's event stream. The profile therefore
rejects physical normalized lines beginning with % after optional spaces/tabs
before parsing (the pinned parser also accepts tab-prefixed directives). Raw BOMs and
source controls are rejected too. This is a conservative policy guard, not an
alternative YAML parser. Schema checks reject unknown/non-string/collection keys
at every applicable level.

## Bounds and diagnostics

- The IO adapter checks a maximum 8192-byte file size before buffer allocation.
  It uses the existing exact-read/growth, strict UTF-8 and source-control policy.
- The pure decoder also checks UTF-8 byte count and source text validity.
- Before parsing: at most 256 normalized lines and 128 raw flow-delimiter
  characters. The latter conservatively counts brackets/braces inside comments
  and strings too, so it may reject otherwise valid YAML.
- Before composition: at most 512 events, collection depth 3, and single-source-line
  decoded scalars of at most 1024 characters. Dependency admission is 64 entries.

parseEvents parses the admitted input before returning events. Event/depth checks
bound composition, **not parser-time recursion or allocation**. Input admission
is not a stack, memory, latency or hostile-filesystem guarantee. Same-size file
changes are not detected; nothing here establishes a locked atomic snapshot.

Maintained parser/composer errors keep real source bounds and use its line-break-
normalized text for excerpts. Composed nodes have no positions: schema errors
name logical fields without invented line/column anchors. Source and manifest
inspection JSON protocols remain separate; no fake coordinate conversion is made.

## Evidence and remaining work

The suite exercises positive quoting/comments/CRLF cases, nonexistent paths,
strict scalar typing, required/unknown fields, duplicate and escaped keys,
anchors/aliases/tags/directives/multiple documents, decoded controls, namespace/
path rules and byte/event/depth admission. The pure decoder-to-planner test covers
two packages without claiming filesystem loading or source checking. Existing
source loader defaults remain 65536 bytes; manifest loading selects the smaller
cap through loadSourceWithin.

[Canonical local dependency/root loading and multi-root check/run](local-packages.md)
are now implemented with explicit --package selection. Workspace-member manifest
syntax, locks/content hashes, remote dependencies and scripts are not implemented.
[Scaffolding](project-creation.md) emits a manifest by default with namespace App;
--module-prefix PREFIX overrides it and --source-only omits the manifest.
