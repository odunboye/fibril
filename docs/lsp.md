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
| Definition | Same-file lexical navigation; checked project/package navigation through aliases and re-exports |
| References | **Same file only**, with includeDeclaration handling |
| Document symbols | Authored declarations reported by the compiler |
| Hover | Builtin/Prelude documentation or an authored-definition excerpt; **not general inferred types** |
| Formatting | Compiler formatting returned as edits, never written by the server; compiler layout policy, not configurable tab/width formatting |
| Rename | Compiler's capture-checked **standalone same-file** preview, returned as versioned documentChanges; named modules/imports remain unsupported |
| Workspace folders and disk changes | Multiple workspace roots; polling of observed sources/directories; explicit watched-file notifications also accepted |

Rename is advertised only when the client supports versioned documentChanges.
Completion, signature help, project-wide references/rename, semantic tokens,
code actions and workspace symbols are not advertised or implemented yet.

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
- `gr`: same-file references;
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

Local symbols, formatting, references and rename do not require a valid project
manifest or a successfully checked import graph. They remain available while
project metadata is broken; checked cross-file definition still requires checking.

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

The 22-test dedicated suite covers framing, UTF-16/CRLF, unsaved changes, imports and
re-exports, package libraries, dependent invalidation, external disk edits,
rename/format safety, cancellation, stale responses, deadlines, URI/path escapes,
malformed JSON and an actual headless Neovim LSP connection. Neovim-specific
coverage is skipped when Neovim is unavailable; protocol/compiler tests remain.

Validation on this branch passed the unit/property phase, 161 CLI tests, 19 native
emitter tests, 9 interactive CLI tests, all 22 dedicated LSP tests and 7 legacy
editor tests. The focused IO suites also passed (285 hosted checks plus runtime
and differential suites). The real Neovim test used Neovim 0.12.5; the client
uses APIs available in 0.10+, but older versions were not exercised here.
`make -j8 handbook` also passed all 16 handbook tests after registering the
previously unindexed IO pages alongside this LSP reference.
