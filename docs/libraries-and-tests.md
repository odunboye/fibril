# Standalone libraries and pure test suites

## Use cases and status

**Implemented:** write, check and test a reusable Fibril library without inventing
an application Main. For example, develop Boolean/domain validation helpers before
an email server imports them. Prefer one application with helper modules when no
reusable boundary is needed. This adds tooling and checking coverage, not new core
expressiveness, implicit imports, algebraic-law proofs or a backend runtime.

~~~sh
fibril new email-core --lib --module-prefix Email.Core
cd email-core
fibril check
fibril test
~~~

The scaffold has a real Fibril identity function and a Fibril-authored Bool test.
The default prefix is App, as for app scaffolds; choose a distinct explicit prefix
when composing packages. --lib and --source-only conflict in either order. No
application Main, dummy entry, hooks, fetched framework or native code is created.
The same fresh-root/exclusive-write/partial-error rules apply, including additional
private parent-first namespace directories. See [project creation](project-creation.md).

![Library checking and test boundary](diagrams/libraries-and-tests.svg)

## One package format, optional application entry

~~~yaml
schema: 1
name: email-core
module-prefix: Email.Core
source-dir: src
foundation: de-morgan
modules: [Email.Core]
test-package: test
dependencies: {}
~~~

entry: Main remains optional. New app and library scaffolds use a separate test/
package with its own manifest, namespace, source root and direct dependency on
the parent. The app starter returns True until replaced with real assertions; it
does not test application IO. An app may also list modules.
There is no separate app/lib kernel or rigid package-kind field.

- modules is an explicit sequence of unique module-name strings owned by this
  package's component prefix. At most 32 are admitted in each manifest, and the
  combined inventory/graph is still bounded globally. Mapping/scalar/nested
  sequence values, non-string names, Main, foreign prefixes and duplicates reject.
- test-package is a relative child-directory path without dot/parent components;
  its canonical package directory must remain inside the parent. Its own manifest
  uses tests to select an owned pure Bool suite and must declare a direct local
  dependency on the same canonical parent package. The two fields are exclusive.
  Legacy inline tests remains supported for existing manifests.
- A root without entry needs a **nonempty** modules inventory for check/test.
  Legacy dependency manifests without inventories remain decodable/loadable.
- Every listed module throughout the declared local dependency closure is seeded
  with its own package identity and checked, even when the root never imports it.
  Imports may reach further source modules under ordinary permissions.

Inventories are checking roots, **not** implicit imports, a module-export whitelist
or complete filesystem crawling. A consumer may import an unlisted owned module;
that source and its reachable bodies are checked normally. Library check returns
an inventory acceptance report, not a fabricated runtime term. Library graph JSON
has entry null. run still requires an actual entry: Main.

## Independent checking and visibility

Within each checking pass, seeds and the selected entry share one source
traversal/cache: 32 modules, depth 32, 524288 aggregate source bytes and existing
per-file/parser limits. All definitions share the ordinary 200000 expanded-core
budget. Private/unused declarations in inventoried/reachable modules are checked.
Source and core budgets do not restart per module or dependency in that pass.
For a separate test package, test first checks the parent, then separately loads
and checks the test package and its dependency closure; budgets restart between
those two passes. The filesystem reads are not one atomic snapshot.

The [local package rules](local-packages.md) still apply: exact canonical paths,
unique prefix ownership, direct-only package permission before cache reuse, and
explicit source imports for exported bindings/schemas/providers. Inventory
membership grants no extra visibility or implementation lookup privilege.

The selected suite must be terminal within its own package graph: another source module cannot import the selected test
entry. Listing the suite itself in modules is allowed; it is deduplicated and
placed last only after that import-conflict check. This first implementation does
not retain an executable entry while checking arbitrary later dependent modules.

## Meaningful pass, failure and error

A suite has an ordinary checked declaration:

~~~fibril
module TestSuite.Suite
import Email.Core

main : Bool
main = Email.Core.identity True
~~~

fibril test (or test --package PATH) checks the full inventory/import graph and
its own unrestricted main before evaluation. It then checks main against Bool,
reference-normalizes with fuel 128, and independently checks the result again:

- True: successful suite, exit zero.
- False: test failure, nonzero.
- Fuel exhaustion, wrong type, missing/erased main or another normal form: error,
  nonzero. Exhaustion is never treated as pass or False.

check never evaluates the suite; if it is listed/imported, its declarations are
checked normally. test does **not** prepare/execute console IO, including an app's
Main. An IO-valued test entry is rejected; printed text is not an assertion signal.
The host prints the suite report, not source-language test effects. Failures go to
stderr; there are no per-assertion names/locations or automatic test discovery.

Fuel bounds reduction contractions, not time, stack or memory. A passing Bool is
one authored suite's result, not quantified property coverage or a proof of laws.
No test isolation, network mocks, effects, filesystem fixtures, shrinking/property
test library or asynchronous test runner is implemented in Fibril yet.

## Example, evidence and limitations

The [Boolean library manifest](../examples/packages/boolean-library/fibril.yaml)
lists a [linear negate function](../examples/packages/boolean-library/src/Algebra/Boolean.fib)
and a [suite checking both Boolean inputs](../examples/packages/boolean-library/src/Algebra/Boolean/Tests.fib).
Run from the compiler project:

~~~sh
./build/exec/fibril check --package examples/packages/boolean-library/fibril.yaml
./build/exec/fibril test --package examples/packages/boolean-library/fibril.yaml
~~~

Tests cover standalone check/run rejection, True/False, wrong IO type, finite fuel
exhaustion, no application IO execution, invalid private inventory bodies,
inventory-without-import visibility, transitive dependency inventories, shared
32/33-module budgets, malformed schema, suite-in-inventory and terminal-suite
conflicts. Creation tests exercise every represented directory/file failure.

The parent retains the existing 16-component/1024-character namespace admission;
the fixed child namespace does not append a suffix to it. Actual filesystem
component/path limits can still make creation fail and leave reported partial output.

YAML still uses the pinned maintained parser, with no aliases/anchors/tags/directives,
bounded events/collection depth and strict scalar fields. Sequences are now
supported specifically for modules; they do not authorize other sequence fields.
See [manifest admission](manifests.md). No lock, content hash, atomic filesystem
snapshot or sandbox guarantee is added. The existing [host Idris test harness](testing.md)
remains separate and still uses pack/Hedgehog to test the compiler itself.
