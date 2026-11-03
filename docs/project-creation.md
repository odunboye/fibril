# Create a project

## Use cases

**Implemented bootstrap tool:** start a small, runnable Fibril console project
without copying an example directory or remembering the entry-module layout.
Use dry-run to inspect the fixed file plan before making changes. Keep an existing
project untouched: init/merging into an existing directory is not implemented.

~~~sh
fibril new mailer
# or preview only:
fibril new mailer --template console --dry-run

cd mailer
fibril check
fibril run
fibril test
~~~

The program prints Hello from mailer!. The tool does not run it automatically.
Only the console template exists; web/server/mobile scaffolds must wait for real
supported deployment paths, not produce misleading placeholder applications.

![Project creation boundary](diagrams/project-creation.svg)

## Generated files

~~~text
mailer/
  .gitignore
  fibril.yaml
  README.md
  src/
    Main.fib
  test/
    fibril.yaml
    src/TestSuite/Suite.fib
~~~

Main is an ordinary named module with main : IO Unit and a Prelude putStrLn call.
By default, fibril.yaml and a package README are emitted using the explicit
default namespace App. --module-prefix overrides App; it is not inferred from
the project slug. A separate local test package with a registered Bool smoke suite is included too.
--source-only omits both manifest and suite and uses source-root commands. Neither mode creates a lockfile, Git
repository, build script or dependency installation; no hooks/templates are
fetched/executed. Bare commands select only ./fibril.yaml; parent search and workspace-member
discovery are not implemented.

## Explicit local package scaffold

~~~sh
fibril new mailer --module-prefix Mailer
cd mailer
fibril check
fibril run
fibril test
~~~

The default scaffold includes fibril.yaml with schema 1, quoted name/module-prefix, source-dir
src, foundation de-morgan, entry Main, test-package: test and empty dependencies. The generated README
uses these package commands. App is a convenience default shared by new projects;
packages used together need distinct owned prefixes, so override it when composing
multiple packages. The planner rejects overlapping namespaces rather than guessing.
Main remains the separate application entry. The child test package owns
TestSuite (or SpecSuite if the parent owns TestSuite) and directly depends on
the parent. No reusable application library is invented. The parent prefix is
App or an explicit override, never derived from the slug; it uses the existing
16-component/1024-character profile and excludes Main and its descendants.

The app suite starts with main : Bool returning True. It is a starter smoke test,
not evidence that the application's behavior or IO is correct. Replace True with
application assertions. fibril test checks the app and suite but never executes
application IO; changing the suite to False fails with nonzero status. See
[library/test boundaries](libraries-and-tests.md). Dry-run lists the suite path too.

Use this for a project that will add local package dependencies. Use
fibril new mailer --source-only for a small single-root experiment. This adds
workflow convenience, not language expressiveness or a new checking rule.
Both modes use the same fresh-root/exclusive-file writer and partial-error policy;
no locks, fetching, hooks, parent-directory search or existing-directory merging.
Package metadata is generated only after validation; normal --package checking
still independently checks source. Dry-run includes the manifest and test paths but makes
no filesystem probes or acceptance promises.

## Standalone libraries

Use fibril new email-core --lib --module-prefix Email.Core, then fibril check
and fibril test. This generates an owned module, an actual pure Bool test module,
a parent manifest with modules/test-package but no entry, plus a child manifest
and suite under test/. No dummy Main is generated. --lib conflicts with --source-only. The same
exclusive-write and partial-output policy applies. See the complete
[library/test workflow](libraries-and-tests.md), its realistic example and limitations.

## Names and arguments

NAME is one relative directory component, 1..64 ASCII characters, starting with
a lowercase letter and followed by lowercase letters, digits, underscore or
hyphen. This is a conservative scaffolding input profile, not a language/module
identifier or finalized package-identity rule. Main stays Main regardless of the
directory slug. Paths, dots, separators, whitespace, controls and quotes are
rejected before mutation.

--lib, --template console, --module-prefix PREFIX, --source-only and --dry-run may appear before/after the name. Duplicate or
unknown flags, extra operands and unsupported templates fail without writes.
--source-only and --module-prefix are mutually exclusive in either order.
fibril new --help describes this command. No force/overwrite option is provided.

Dry-run is a pure plan preview: it does not create temporary files or probe the
filesystem. It can preview an existing name but does not promise that real
creation will succeed or that the destination is absent/writable.

## Safety contract

The first writer targets the POSIX bootstrap and a **trusted, stable working
directory**. It does not protect against hostile concurrent path/ancestor rename,
symlink replacement, another malicious process running as the same user, or
filesystem sandbox escapes. It uses pathname operations, not directory-pinned
capabilities. Do not run it in an attacker-controlled directory or as a privileged
service on untrusted names.

[Runtime.Project](../src/Fibril/Runtime/Project.idr) uses:

- One mkdir(..., 0700) admission attempt, not exists-then-create. Any existing
  destination entry, including a symlink or dangling symlink, is an error.
- A private src directory. Both directory modes may be further restricted by
  the user's umask.
- C11/POSIX fopen(..., "wx") for every fixed file: exclusive creation, never
  ordinary truncating write mode. A null result is reported.
- Checked fputs and fclose results; an opened handle is closed even after a
  represented write error. Buffered close errors are reported.

A successful mkdir makes one competing creator win; it does not make all file
creation atomic or crash-durable. Errors after admission can leave a partial
project. The command identifies that possibility and performs **no recursive
rollback or cleanup**. Inspect partial output manually before retrying; do not
blindly remove a directory that another process may have edited.

The current macOS/Chez writer is exercised end to end. Host dispatch recognizes
Chez darwin/unix and RefC macOS/Linux identifiers; Chez unix includes Linux/BSD,
not a claim that every platform/backend combination was integration-tested.
Exclusive fopen semantics and the libc FFI must hold on the deployment host.
Windows and unknown host identifiers are refused; this is not Windows support.

## Architecture and evidence

[Project.Template](../src/Fibril/Project/Template.idr) is a pure fixed template and
name validator. [Project.New](../src/Fibril/Project/New.idr) parses arguments and
orchestrates effects. Neither imports the checker, language parser or elaborator. The template reuses
the pure workspace namespace profile, not a source acceptance result.
Main only dispatches this tool; the kernel does not acquire project-management
logic. The small libc adapter is bootstrap host IO, not a source-language FFI.

This keeps one user-facing CLI without coupling package tools to compiler
internals. Templates may become versioned packages later. No automatic executable
plugin discovery or remote hooks are authorized by this command.

Tests create projects only in temporary working directories, verify generated
bytes/permissions, check/run the source, and exercise dry-run/no-mutation,
invalid/duplicate flags, existing entries, symlinks, permission errors and
concurrent admission. Injectable host callbacks test stop-on-failure and partial
output reporting at orchestration boundaries. They do not simulate every real
native write/close failure or hostile filesystem race. Read-only parallel review
verified the primitive choices and caught/fixed the Chez Unix host-guard issue.

[Explicit local package loading](local-packages.md) and namespace-selected
manifest scaffolding now work. Existing-directory init needs a separate safety contract. A pure REPL can reuse checking/evaluation later; it is
not introduced by scaffolding.
