# Fibril language server

Status: an initial, editor-independent LSP server, with a thin Neovim client.
It is a Python 3.10+ stdio frontend to the actual Idris compiler services, not a
second parser/typechecker or an LSP implementation embedded in the kernel.
No third-party Python packages are needed. This slice targets POSIX systems.

## Start the server

From this checkout:

```sh
make -j8 build
python3 tools/fibril_lsp.py --fibril ./build/exec/fibril
```

The process speaks Content-Length-framed JSON-RPC on stdin/stdout, not an
interactive command prompt. Configure any LSP client to launch that command.
Paths in editor configuration should be absolute. The default compiler path is
this checkout's `build/exec/fibril`, never a workspace-supplied executable.
`--timeout SECONDS` controls each compiler subprocess deadline (default 15).

## Implemented services

| Service | Scope |
| --- | --- |
| Initialize, shutdown, exit, cancellation | Stdio JSON-RPC, bounded framing, UTF-8 messages |
| Document open/change/save/close | Full or ordered incremental changes; monotonic versions |
| Positions | LSP UTF-16, converted to/from compiler Unicode-scalar offsets; CRLF and non-BMP text supported |
| Push diagnostics | Dirty buffers, imported dependencies, applications and entry-free library inventories |
| Definition | Same-file lexical navigation; checked symbol and module/file navigation on import names, aliases, qualified prefixes and re-export selectors; LocationLinks when supported |
| References | Canonical symbol/module occurrences across the **checked application graph or library inventory**, with declaration filtering and duplicate suppression; standalone files retain lexical references |
| Document symbols | Authored declarations reported by the compiler |
| Hover | Builtin/Prelude documentation or an authored-definition excerpt; **not general inferred types** |
| Formatting | Compiler formatting returned as edits, never written by the server; compiler layout policy, not configurable tab/width formatting |
| Rename | Compiler's capture-checked **standalone same-file** preview, returned as versioned documentChanges; named modules/imports remain unsupported |
| Workspace folders and disk changes | Multiple workspace roots; polling of observed sources/directories; explicit watched-file notifications also accepted |

| Completion | Compiler scope at the cursor: local binders, checked visible globals and selected imports/aliases, with type and quantity details; matching expected types rank first. Syntax-only fallback is marked incomplete. |
| Project rename | In a manifest/source-root project: checked-graph references become versioned multi-file edits; plain identifiers only, refused if the new name already appears in any affected file (conservative, not a capture check) |

Completion queries run against a private copy of the dirty-buffer snapshot. A fresh
unbound identifier stands in for the identifier under the caret; the compiler
reports its local context only after checking that context's type formation.
The query never executes source programs or writes editor/workspace files.
Existing request cancellation, deadlines and document/disk freshness checks apply.

Nearest local binders shadow globals. Imports follow the compiler's normal
selection, alias and export visibility rules. Completion replaces the whole
identifier, including any suffix after the caret, using UTF-16 edit positions.
Type-compatible values rank first; functions and other visible names remain
available. Quantity details describe declarations, not a guarantee that inserting
a candidate satisfies the surrounding program's usage constraints. Complex types
can retain core syntax in the display.

If a parse error, an earlier error, or an unreachable module prevents checking the
query site, the server falls back to current-file/Prelude symbols with
`isIncomplete: true` and the detail `Syntax only; checked scope unavailable`.
Such fallback suggestions carry no scope or type claim. The compiler attaches an
optional `completionScope` to the query's JSON diagnostic; ordinary diagnostics
keep their existing fields. This metadata is editor information, not a typing
certificate or an accepted partially checked program.

Rename is advertised only when the client supports versioned documentChanges.
Signature help, semantic tokens, code actions and workspace symbols are not
advertised or implemented yet.

## Neovim: standard LSP instead of custom commands

Neovim 0.10+ needs no lspconfig/plugin-manager dependency:

```lua
vim.opt.runtimepath:append('/absolute/path/to/fibril/editors/nvim')
require('fibril').setup({
  -- Optional: otherwise uses this checkout's compiler.
  fibril = '/absolute/path/to/fibril/build/exec/fibril',
})
vim.cmd('syntax enable')
```

Open a `.fib` file. Standard diagnostics and language-server requests provide:

- `gd`: definition;
- `gr`: references across the checked scope;
- `K`: documentation/declaration excerpt;
- `<leader>rn`: guarded standalone rename;
- `<leader>f`: formatting.

Pass `keymaps = false` to keep your own mappings. `on_attach`, `capabilities`,
`cmd`, `python`, `root_dir` and `init_options` can be supplied. This module only
configures `vim.lsp.start`; other editors use the same server directly.
Existing Vim syntax files are reused. Enabling this setup suppresses/removes the
legacy buffer commands in Neovim; Vim and unconfigured legacy clients still work.
The legacy integration is documented in [editor-highlighting.md](editor-highlighting.md).

## Project configuration

The default Neovim root prefers the Git repository, then the nearest
`fibril.yaml`, then the file's directory. The server detects a nearest package
manifest; otherwise it infers a source root from the module header and prefers
`Main.fib` as entry when present. Headerless files can be checked standalone.

For an explicit single-root project:

```lua
require('fibril').setup({
  init_options = { sourceDir = 'src', entry = 'src/Main.fib' },
})
```

For a specific package, use `init_options = { manifest = 'app/fibril.yaml' }`.
Option paths are relative to the workspace root (or absolute within it), not
relative to sourceDir. They cannot escape that root. For sibling local packages,
open their common parent as the workspace, or provide an appropriate `root_dir`.
Declared package dependencies outside the snapshot are rejected before loading.
Library packages need their normal explicit `modules` inventory, not a fake main.
An open named module outside the checked entry/inventory receives a scope warning
rather than being silently represented as checked.

Local symbols, formatting and standalone rename do not require a valid project
manifest or a successfully checked import graph. Checked project definitions and
references require the graph to check; they never fall back to name-text matches.

## Navigation scope and identity

The compiler builds a shared navigation index from the successfully checked
graph, checked export origins, lexical AST scopes and checker-produced recursive
self-call sites. A symbol's identity is its defining file and declaration span,
not its spelling. Module identities point at module headers. Imported names,
aliases and qualified module prefixes link to the imported module file; a
re-exported symbol still links to its original declaration. Import selectors
count as symbol occurrences, while imports/aliases/qualifiers count as module
uses. includeDeclaration excludes authored definition/signature sites and module
headers, not re-export selectors or alias mentions.

References are limited to the loaded application closure or explicit library
inventory. Inventory-only modules are included; unrelated workspace files and
reverse package dependants are not guessed or automatically discovered. Same
spelled local binders/private names remain separate. Ambiguous or invalid graphs
produce checking failures rather than guessed results. Project rename reuses
these references; it needs a project that checks, and rejects module/qualified names.

CLI access is also available through `references --source-dir ROOT --entry ENTRY
LINE COLUMN PATH` and `references --package MANIFEST LINE COLUMN PATH`.

The compiler also exposes `fibril check --json --package MANIFEST`: version-2
source-backed diagnostics for applications and library inventories.

## Snapshot and concurrency contract

All compiler services operate on private temporary copies of `.fib` sources and
`fibril.yaml` manifests with **all applicable open buffers overlaid**. They never
save original files, execute Fibril programs, run package hooks or invoke a shell.
Compiler errors/diagnostics are data; stdout is reserved for framed LSP messages.
Source paths/ranges are mapped back only to known snapshot files. Responses with
foreign paths, mismatched snapshots or unsupported coordinates are rejected.

A responsive protocol reader runs alongside one serialized compiler worker.
New document/workspace state cancels obsolete work, and stale responses are
rejected with ContentModified. Cancellation/deadlines terminate only that
request's newly created subprocess group. Diagnostics carry open-buffer versions;
changes to imported dirty buffers or observed closed files trigger rechecking.
Disk metadata is rechecked before returning edits/navigation. Formatting edits
still require the client's normal post-response stale-edit safeguards.

Limits: 8 MiB protocol bodies and source snapshots, 64 KiB per source file,
1024 snapshot files, 4096 directories, 64 open documents/outstanding requests,
and 64 package dependency manifests. Compiler limits additionally apply.
Current analysis rebuilds snapshots and invokes compiler services; it is **not an
incremental typechecker or cached build daemon**. Large workspaces may require a
narrower root. Directory/file identity checks and symlink avoidance are defense
in depth, not an atomic filesystem snapshot or hostile-filesystem sandbox.
Blocking/faulting host filesystems are not covered by subprocess deadlines.

## Validation

```sh
make -j8 lsp-test
make -j8 test editor-test
```

The 29-test dedicated suite covers framing, UTF-16/CRLF, unsaved changes, imports and
re-exports, package libraries, dependent invalidation, external disk edits,
rename/format safety, cancellation, stale responses, deadlines, URI/path escapes,
malformed JSON and an actual headless Neovim LSP connection. Neovim-specific
coverage is skipped when Neovim is unavailable; protocol/compiler tests remain.

Validation on this branch passed the unit/property phase, 161 CLI tests, 19 native
emitter tests, 9 interactive CLI tests, all 29 dedicated LSP tests and 7 legacy
editor tests. The focused IO suites also passed (285 hosted checks plus runtime
and differential suites). The real Neovim test used Neovim 0.12.5; the client
uses APIs available in 0.10+, but older versions were not exercised here.
Navigation coverage includes an actual Neovim import-to-file jump, cross-file
reference results, re-export diamonds, shadowing, private/ambiguous-name rejection,
recursive self calls and application versus library-inventory scope.

CLI-consuming Make suites now depend on `unit-test`: package testing can reinstall
or relink the compiler even after `build`. An initial parallel regression run hit
that race and the old intentional no-module-navigation assertions; the dependency
ordering and expectations were corrected, and the complete rerun passed.
`make -j8 handbook` also passed all 16 handbook tests after registering the
previously unindexed IO pages alongside this LSP reference.
