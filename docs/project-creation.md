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
fibril check --source-dir src src/Main.fib
fibril run --source-dir src src/Main.fib
~~~

The program prints Hello from mailer!. The tool does not run it automatically.
Only the console template exists; web/server/mobile scaffolds must wait for real
supported deployment paths, not produce misleading placeholder applications.

![Project creation boundary](diagrams/project-creation.svg)

## Generated files

~~~text
mailer/
  .gitignore
  README.md
  src/
    Main.fib
~~~

Main is an ordinary named module with main : IO Unit and a Prelude putStrLn call.
The README includes the explicit check/run commands. No package manifest, lockfile,
dependencies, Git repository, build script, install hook or external template is
created/fetched/executed. [Manifest inspection](manifests.md) exists, but implicit
project/workspace-member discovery and generated manifests remain future work. This is source scaffolding, not a new acceptance rule.

## Names and arguments

NAME is one relative directory component, 1..64 ASCII characters, starting with
a lowercase letter and followed by lowercase letters, digits, underscore or
hyphen. This is a conservative scaffolding input profile, not a language/module
identifier or finalized package-identity rule. Main stays Main regardless of the
directory slug. Paths, dots, separators, whitespace, controls and quotes are
rejected before mutation.

--template console and --dry-run may appear before/after the name. Duplicate or
unknown flags, extra operands and unsupported templates fail without writes.
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
orchestrates effects. Neither imports the checker, parser or elaborator.
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

[Explicit local package loading](local-packages.md) now works. Next: integrate
explicit namespace selection and generated package metadata
and safe init behavior. A pure REPL can reuse checking/evaluation later; it is
not introduced by scaffolding.
