# Neovim and Vim highlighting, checking, and navigation

## Use cases

Use editor commands to check a project, follow definitions, inspect references and preview supported lexical renames without guessing where an authored name came from.

Use explicit navigation/manual edits when project-wide references or rename are needed; those capabilities and a full LSP are not implemented. Formatting and checking should not silently save buffers.

Status: implemented optional Vim-runtime package for the current Fibril subsets.
Includes optional compiler-backed runtime checking and same-file navigation. No Tree-sitter grammar,
LSP server, semantic tokens, or cross-file navigation is added.

## Try a clean Neovim session

From the Fibril repository root:

~~~sh
nvim -u NONE -n \
  --cmd "lua vim.opt.runtimepath:prepend(vim.fn.getcwd() .. '/editors/vim')" \
  --cmd 'filetype plugin on' \
  --cmd 'syntax enable' \
  examples/core/hello-world.fib
~~~

This does not install anything or run the Fibril program.

## Persistent setup

Add to your Neovim init.lua, substituting your checkout path:

~~~lua
vim.opt.runtimepath:prepend("/absolute/path/to/fibril/editors/vim")
vim.cmd("filetype plugin on")
vim.cmd("syntax enable")
vim.cmd("runtime! ftdetect/fibril.vim")
~~~

The final command registers detection even if filetype detection was already
enabled before modifying runtimepath. Restart and open a .fib file.

For Vim, add to .vimrc:

~~~vim
execute 'set runtimepath^=' . fnameescape('/absolute/path/to/fibril/editors/vim')
filetype plugin on
syntax enable
runtime! ftdetect/fibril.vim
~~~

An existing nonempty filetype is respected. To explicitly override it for an
already-open buffer, use :setlocal filetype=fibril. :setlocal filetype? and
:setlocal syntax? help diagnose loading.

The package has no plugin-manager dependency, compiler invocation, automatic
execution, external process, network request, or language-server startup.
As with other editor plugins, its Vimscript is trusted local editor code.

## Install in LazyVim

Use a local plugin spec pointing at the runtime directory in your Fibril checkout.
There is no published remote plugin repository to install yet.

1. Create `~/.config/nvim/lua/plugins/fibril.lua`. If your configuration lives
   elsewhere, `:echo stdpath('config')` shows its root; use its `lua/plugins/`
   directory instead.
2. Build the compiler with make build in the Fibril checkout. Add the following,
   replacing both absolute paths with your checkout location. The gd/gD/gr/K and
   <leader>cr/<leader>ck/<leader>cK mappings are optional and affect only Fibril buffers. The <leader>cr mapping
   replaces LazyVim's usual rename action in those buffers with a preview:

~~~lua
return {
  {
    name = "fibril-syntax",
    dir = "/absolute/path/to/fibril/editors/vim",
    lazy = false,
    config = function()
      vim.g.fibril_executable = "/absolute/path/to/fibril/build/exec/fibril"
      vim.cmd("syntax enable")
      vim.cmd("runtime! ftdetect/fibril.vim")

      vim.api.nvim_create_autocmd("FileType", {
        pattern = "fibril",
        callback = function()
          vim.keymap.set("n", "gd", "<Plug>(FibrilDefinition)", {
            buffer = true, remap = true, desc = "Fibril: go to definition",
          })
          vim.keymap.set("n", "K", "<Plug>(FibrilReference)", {
            buffer = true, remap = true, desc = "Fibril: built-in / Prelude reference",
          })
          vim.keymap.set("n", "gD", "<Plug>(FibrilDefinitionProject)", {
            buffer = true, remap = true, desc = "Fibril: project definition",
          })
          vim.keymap.set("n", "gr", "<Plug>(FibrilReferences)", {
            buffer = true, remap = true, desc = "Fibril: references",
          })
          vim.keymap.set("n", "<leader>cr", "<Plug>(FibrilRenamePreview)", {
            buffer = true, remap = true, desc = "Fibril: preview rename",
          })
          vim.keymap.set("n", "<leader>cf", "<Plug>(FibrilFormat)", {
            buffer = true, remap = true, desc = "Fibril: format buffer (no save)",
          })
          vim.keymap.set("n", "<leader>ck", "<Plug>(FibrilCheck)", {
            buffer = true, remap = true, desc = "Fibril: check",
          })
          vim.keymap.set("n", "<leader>cK", "<Plug>(FibrilCheckProject)", {
            buffer = true, remap = true, desc = "Fibril: check project",
          })
        end,
      })
    end,
  },
}
~~~

The dir must point to **editors/vim**, not the repository root. For this project's
usual local layout it might be `/Users/yourname/dev/idris2/projects/fibril/editors/vim`.
The directory must already exist; lazy.nvim loads these local files rather than
fetching a plugin. Keeping the checkout updated also updates the runtime files.

3. Restart Neovim and open `examples/core/do-result.fib` from that checkout.
   On line 12, place the cursor on message. In a saved, unmodified buffer, gd
   jumps to its binding on line 11; gr opens its declaration/use location list.
   Press Enter on a result to navigate, or :lclose to close the list. Without
   mappings, use :FibrilDefinition and :FibrilReferences. Press <leader>cr to
   start :FibrilRenamePreview, type a new name, and press Enter. For example,
   :FibrilRenamePreview greetingText opens a read-only scratch diff; :close
   dismisses it. No source is modified or saved. These queries are same-file
   only and do not type-check the source. For runtime checking, run :FibrilCheck
   or press <leader>ck. This checks without executing program IO.
   For multi-file checking, open the saved entry buffer (usually Main.fib), then
   configure its source root explicitly:

~~~vim
:lua vim.b.fibril_source_dir = "/absolute/path/to/project/sources"
:FibrilCheckProject
~~~

   Or press <leader>cK (uppercase K) with the optional mapping above. The root
   contains the module hierarchy, not necessarily a nested entry's directory.
   For the bundled example, open examples/modules/checked/Main.fib and set the
   root to the absolute path of examples/modules/checked.

   To persist a root for a single workspace, optionally add this to your own
   lua/config/options.lua:

~~~lua
vim.g.fibril_source_dir = "/absolute/path/to/project/sources"
~~~

   The buffer-local setting overrides this global fallback. Avoid a global root
   when switching between unrelated projects; configure the relevant entry
   buffer instead. Roots are not automatically discovered.

   Dependency points are jumpable only in already-loaded UTF-8 buffers. Open a
   dependency in a split, return to the entry, and rerun the check. Unloaded
   points remain labelled but nonjumpable. Save modified dependencies first.
   See [Project checking in the editor](#project-checking-in-the-editor) for
   snapshot checks and limitations. Neither check command executes program IO.

4. Run `:Lazy` and confirm `fibril-syntax` is loaded. Then check:

~~~vim
:setlocal filetype?
:setlocal syntax?
~~~

Both should report fibril. To inspect an actual token, put the cursor on a keyword
such as if and run:

~~~vim
:echo synIDattr(synID(line('.'), col('.'), 1), 'name')
~~~

The result should be fibrilKeyword. Different token kinds have different groups.
If another configuration assigned a filetype first, explicitly use
`:setlocal filetype=fibril`; automatic detection deliberately respects existing
filetypes. If highlighting was disabled, run `:syntax enable`.

This uses Neovim's built-in syntax engine. You do not need a Fibril Tree-sitter
parser, Mason package, or LSP configuration. Do not add fibril to Tree-sitter's
parser-install list: we have not published a grammar. If custom configuration
forces Tree-sitter onto unsupported filetypes or disables regex highlighting,
exclude fibril from that customization. The supplied runtime does not change your
LazyVim keymaps, formatting, or LSP settings.

To uninstall, remove the plugin spec and restart Neovim. Your Fibril checkout and
source files are unaffected. These steps document lazy.nvim's local-plugin setup;
the automated editor tests exercise the runtime in clean Neovim/Vim sessions,
not a complete LazyVim distribution or its third-party plugins.

## What it highlights

- Ordinary keywords: let/in, case/of, if/then/else.
- Builtin types and Boolean constructors.
- ASCII and Unicode lambda/arrows, annotations, and delimiters.
- Numbers, with contextual 0/1 quantity highlighting.
- Column-one declaration names, including quantity-prefixed headers.
- Console-profile IO, do, and putStrLn spellings.
- Strings, supported escapes, unknown escapes, and invalid raw tabs.
- Line comments and TODO/FIXME/NOTE/XXX markers.

Strings protect comment markers and keywords inside them. Unterminated strings
are colored only through their line, so incomplete editing does not swallow
subsequent declarations. Apostrophes remain part of identifiers.

![Lexical presentation, not semantic checking](diagrams/editor-highlighting.svg)

Groups link to standard editor groups using highlight default link, so your
theme chooses colors and existing custom links are not replaced. For example:

~~~vim
highlight link fibrilQuantity Special
highlight link fibrilDeclaration Identifier
~~~

IO/putStrLn are ordinary resolved prelude/primitive names and can be shadowed;
do is expression syntax. Their lexical highlighting does not prove which binding
is in scope or that an expression is well typed.
Declaration highlighting does not infer whether a name denotes a function,
type, or value. Invalid source can still receive plausible colors.

## Buffer behavior and source

[ftdetect/fibril.vim](../editors/vim/ftdetect/fibril.vim) registers .fib files for
read/new-buffer events without replacing an already assigned filetype.

[ftplugin/fibril.vim](../editors/vim/ftplugin/fibril.vim) sets commentstring to
-- %s, line-comment metadata, and apostrophe-aware word motion. It supplies the
standard undo hook and optional FibrilCheck/FibrilCheckProject/FibrilDefinition/FibrilReferences/
FibrilRenamePreview commands and Plug mappings. It does
not change indentation/formatting or override user keys such as gd.

[syntax/fibril.vim](../editors/vim/syntax/fibril.vim) contains only lexical rules.
Reload guards avoid duplicate setup. No editor code modifies core checking rules,
accepts proofs, or writes source files.

The [offline handbook](handbook.md#code-highlighting) also highlights Fibril and
Idris snippets/source pages. Its local Pandoc grammar is a separate presentation
layer, not this Vim runtime or a shared semantic language service.

## Formatting in Vim and LazyVim

After building the updated compiler and restarting/reloading the runtime, run:

~~~vim
:FibrilFormat
~~~

The optional LazyVim setup above maps <leader>cf to <Plug>(FibrilFormat), replacing
the usual buffer-format action **only in Fibril buffers**. The runtime itself
assigns no default key. This is a manual command, not a Conform/LSP adapter or
format-on-save hook.

It formats the **current buffer**, including unsaved edits and unnamed buffers.
It never saves the source file. The change is one undo block: u restores the
exact pre-format text without discarding earlier unsaved edits. Redo works
normally; an already-canonical buffer creates no change/undo entry. Cursor/view
are retained approximately by line/scalar column, not a semantic token identity.

The formatter is still the conservative
[formatter](formatting.md), including guarded application/lambda/signature/case layout. It handles
already-multiline definitions too, but does not generally reindent all blocks or
reflow record headers/fields and flat do statements. Comments, literal spelling, LF/CRLF, final-newline presence and buffer
encoding/line-ending options are retained. Normal editable UTF-8 buffers with
Unix/CRLF line endings and undo enabled are required; readonly, BOM and special
buffers are refused. NUL-containing buffers and compiler/source-policy errors
leave the buffer unchanged.

The adapter serializes the buffer into a temporary snapshot, sets private
rw------- permissions before writing source content, and invokes the configured
compiler's format --json service with separately quoted arguments. The snapshot
is cleaned up in a finally block on represented success/failure (filesystem
cleanup failures are outside that guarantee). No temporary file is treated as a
project entry or used for import resolution.

Before applying results, it checks the source text, changedtick, window/buffer
identity, file-format options, protocol version and original-text acknowledgement.
Malformed/inconsistent results, removed lines, changed non-whitespace content,
blank lines/endings or a stale buffer are refused without applying edits.
Guarded wrapping may insert continuation lines as part of the same undo block. The producer reparses and checks AST shape;
the editor does not independently implement the Fibril parser. g:fibril_executable
is trusted executable configuration, not an adversarial formatting service.

Other compiler queries still require saved snapshots; formatting is the explicit
exception. Save separately with :write when satisfied. Automatic formatting on
save, cancellation, asynchronous requests and broader indentation/reflow remain
future work. External editor hooks and OS/process crashes are outside these represented
error guarantees.

## Runtime checking in the editor

After configuring g:fibril_executable and saving a .fib buffer, run:

~~~vim
:FibrilCheck
~~~

This invokes [check --json](diagnostics.md#structured-runtime-check-reports).
A rejected program's diagnostics open a window-local location list. Located
frontend errors use their actual scalar point converted to an editor byte column.
Press Enter on a jumpable entry to navigate; :lclose closes the list.

Core type/resource failures have no source provenance, so their entries explicitly
say unlocated and are **nonjumpable**, not attached to a guessed line one.
Decoding failures show their byte offset without treating it as a scalar column.
A real EOF point beyond Vim's last buffer line, or a source point obscured by a
hidden byte-order mark, is shown with its recorded coordinates but remains
nonjumpable. No diagnostic range or subterm location is fabricated.

On acceptance, a new empty check list becomes current and the status/type report
is displayed (up to 512 bytes). No new window opens; prior lists remain in history
(:lolder). Checking never executes IO descriptions or writes source. Results
refer to the saved snapshot; re-run the command after source changes.

The command shares navigation's saved-buffer, UTF-8/line-ending, source snapshot,
compiler-path, and version checks. Exit status 1 is accepted only with a consistent
rejection report; malformed/partial/inconsistent reports leave prior lists intact.
All entries are validated before changing the list, including scalar offset versus
line/column agreement where the buffer representation permits it.

The <Plug>(FibrilCheck) mapping is available; no default key is assigned. The
complete LazyVim example above optionally maps <leader>ck. The undo hook removes
the command and Plug mapping.

This is synchronous, manual, file-based checking, not automatic diagnostics,
unsaved-buffer checking, async cancellation, an incremental checker, or an LSP.
The underlying compiler's experimental typing/resource rules and evidence limits
are unchanged. A displayed acceptance is not a metatheoretic certificate.

## Project checking in the editor

Open the saved **entry** buffer (normally Main.fib), select its explicit source
root, then request a project check:

~~~vim
:let b:fibril_source_dir = '/absolute/path/to/project/sources'
:FibrilCheckProject
~~~

In Neovim the same buffer-local configuration can be set with:

~~~lua
vim.b.fibril_source_dir = "/absolute/path/to/project/sources"
~~~

A global g:fibril_source_dir is an optional fallback. No root is inferred from
the current directory, repository markers, manifests, or file contents. The
buffer-local setting wins. g:fibril_executable remains an executable **path**;
root and entry are separately quoted arguments, including spaces/apostrophes.

This invokes check --json --source-dir ROOT ENTRY and consumes the
[version-2 project report](diagnostics.md#source-aware-project-reports-version-2),
not the version-1 FibrilCheck adapter. Every available project snapshot must match
disk; all already-loaded buffer aliases must also be unmodified UTF-8, with
supported line endings and matching text. Stale dependencies, missing/duplicate/
outside-root source identities, malformed diagnostics, and inconsistent status
leave the prior list intact. All entries are validated before replacing the UI.

Rejection opens a window-local list with each diagnostic's real file path.
Scalar points can jump to an **already-loaded** dependency buffer, converting
against that file's snapshot rather than the entry. Unloaded sources are not
automatically loaded: their entries retain recorded coordinates and an
"open source and rerun project check" label, but are nonjumpable. Open the file
in a split (or keep it loaded with hidden enabled), return to the entry, and
rerun to enable its jumps. This avoids hidden buffer-read hooks and assumptions
about the encoding of a file that Vim has not loaded.

Core failures, decoding byte offsets, unavailable source text, EOF beyond the
last buffer line, and unsupported snapshot line endings never acquire guessed
jumps. Known-empty sources remain distinct from unavailable snapshots.
Acceptance creates an empty project-check list and displays the type/status;
IO descriptions are never executed. No source is written or automatically saved.

The optional <Plug>(FibrilCheckProject) mapping and command are buffer-local and
removed by the undo hook; no default key is assigned. For example, a personal
LazyVim FileType mapping may use <leader>cK for this Plug alongside <leader>ck
for single-file checks.

This is a manual synchronous snapshot check, not a filesystem transaction or
live diagnostic subscription. Rerun after edits; locations can become stale
after display. Project buffers with unsaved changes are not checked.
Project-wide references/rename, automatic loading from diagnostic lists, LSP,
cancellation, and incremental checking remain separate work.

## Built-in and Prelude references

Use :FibrilReference (or the optional LazyVim K mapping above) on a supported
built-in or an unshadowed Prelude name. Both definition commands fall back to
this service when no source definition is found.

- String, Unit, Bool, Type, and IO open concise **documentation**, not invented
  source definitions. IO is a primitive constructor; it is not declared in
  Prelude.fib. Primitive prim* names have an infrastructure reference too.
- putStrLn, pure, bind, map, String/Bool wrappers, and other ordinary Prelude
  names open the actual declaration in the compiler's **bundled Prelude source
  snapshot**, positioned at its definition name.

Both views are read-only, nonmodifiable scratch splits without swapfiles or
source writes. Close with :close. The source snapshot is explicitly labelled:
it is not a guessed filesystem path or necessarily the current checkout's
stdlib/Prelude.fib. It is the embedded source used by that compiler build.
It is not an editable workspace file; return to the original source for further
compiler queries.

Lookup parses the document and respects lexical shadowing. A local IO or
putStrLn does not become a primitive/Prelude link. Comments, strings, qualified
references, module headers, and unknown names are not text-matched into links.
This is syntax/lexical reference information, not program acceptance, a proof,
or a complete language-keyword manual. Incomplete syntax may still reject the
request. No general hover server, LSP, web lookup, or native effect execution is
involved. The optional <Plug>(FibrilReference) mapping has no default key and is
removed with the buffer-local command by the undo hook.

The corresponding compiler API is:

~~~sh
./build/exec/fibril reference LINE COLUMN PATH
~~~

Version-1 JSON contains reference: null or a tagged object:
builtin-documentation has name/lines and no source range;
bundled-prelude-source has name/source/range. The range belongs to the supplied
bundled source, never to the query buffer.

## Project definitions in the editor

Use :FibrilDefinitionProject for checked source-aware lookup; the ordinary
:FibrilDefinition / gd remains same-file. The optional LazyVim example above maps
gD to <Plug>(FibrilDefinitionProject), only in Fibril buffers.

The source-root setting is shared with project checking. Entry selection uses
b:fibril_project_entry, then g:fibril_project_entry, then the current file.
For a single workspace, configure both globals in lua/config/options.lua:

~~~lua
vim.g.fibril_source_dir = "/absolute/path/to/project/sources"
vim.g.fibril_project_entry = "/absolute/path/to/project/sources/Main.fib"
~~~

Buffer-local settings override globals for multi-project sessions. Library
queries need an explicit entry: a library is not assumed to have its own main.
If only the entry buffer has buffer-local settings, configure the library buffer
too before making further project queries there.

Place the cursor on the final identifier in Text.Greeting.greet and invoke the
command. It checks the project, verifies query/entry/root identities and all
reported source snapshots, and opens the target file at the actual definition
name. Unloaded targets are opened automatically as UTF-8; you do not need to
pre-open dependencies. Local definitions use the same traversal. Source
buffers must be saved, unmodified UTF-8; no source is automatically saved.

Null targets, malformed packets, stale
snapshots, hidden/unsupported positions, and modified dependency aliases do not
produce guessed jumps. No location list is replaced. Buffer-enter hooks are
outside the compiler's control; after switching buffers, identity/encoding/text
are checked again before positioning, including all available project snapshots.
If a read/enter hook changes text or identity, the file may remain open but no
snapshot-based cursor jump is applied; the adapter warns and preserves the
changed text. Opening uses normal editor hooks and does not bypass Vim security
settings or overwrite modified buffers. This is manual snapshot navigation, not a
live index or atomic filesystem transaction.

The command and Plug mapping are removed by the ftplugin undo hook. No default
key is assigned by the runtime; the LazyVim gD mapping is an optional user choice.
IO descriptions are not executed. Project references/rename remain unimplemented.
Project checking still does not automatically load dependency buffers; automatic
opening is performed only when explicitly navigating to a definition.

## Checked project definition API

The same-file gd mapping is unchanged. For explicit project lookup, the compiler
now provides:

~~~sh
./build/exec/fibril definition --source-dir ROOT --entry ENTRY LINE COLUMN PATH
~~~

ENTRY selects the checked program; PATH selects any reachable source file to
query, including a library without its own main. Paths are relative to the
process working directory unless absolute. Coordinates are one-based Unicode
scalars, with the same decimal bounds as other location queries.

The service checks the complete graph before lookup. It uses a shared lexical
traversal for local bindings and direct imported qualified exports. Own-qualified
earlier definitions, including private helpers, resolve within their module.
Imported private definitions and transitive leakage are rejected by checking
before any successful navigation packet is emitted.

Only a qualified reference's **final identifier** is selectable. Module
qualifiers, dots, imports, whitespace, strings, and unknown/prelude targets return
definition: null. Parentheses do not become part of the selected identifier.
A local variable with the same spelling as a module component cannot capture a
qualified reference.

A successful version-2 packet contains entry, root, query, checked: true,
sources, and definition. Sources are exact path/text snapshots of the reachable
project. Definition is null or a path/range object; its range selects the
definition's actual name token, not its signature or an invented body location.
A type/loading failure or query file outside the graph reports stderr with
nonzero status and no success packet. IO descriptions are not executed.

[prepareProjectDefinition](../src/Fibril/Driver/ProjectNavigation.idr) exposes
structured data separately from JSON rendering. The generic
[documentReferencesUsing](../src/Fibril/Source/Navigation.idr) traversal takes
caller-supplied target identities and qualified bindings; those raw inputs are
not checking certificates. The project service admits them only after checking.

FibrilDefinitionProject consumes this version-2 API with snapshot validation and
validated automatic target opening. The ordinary version-1 definition client remains
separate and rejects version 2 rather than attach a dependency span to the
current buffer. Project-wide
references, rename, stable symbol IDs, and incremental
caching remain separate work.

## Parsed document symbols

The compiler now exposes a syntax-only declaration service:

~~~sh
./build/exec/fibril symbols examples/core/io-map.fib
./build/exec/fibril symbols stdlib/Prelude.fib
~~~

On success, stdout contains one JSON object with version 1, an explicit
coordinates label, and a symbols array in source order. Each symbol has name,
quantity ("0", "1", or "unrestricted"), range, selection, definitionSelection,
and exported (whether an export marker was parsed; not checked accessibility).
range covers the signature/definition pair, including a signature quantity but
excluding trailing whitespace/comments. selection selects the signature's actual
name token; definitionSelection selects its definition's actual name token.

Each range is half-open, with start/end positions containing zero-based scalar
offset and one-based line/column. Unicode scalars are not UTF-8 bytes, terminal
cells, or LSP UTF-16 units. CRLF consumes two offsets but advances one line.
An editor must convert coordinates against the exact source snapshot.

[Source.Symbol](../src/Fibril/Source/Symbol.idr) accepts a source String, so future
editor integrations can use unsaved buffers without temporary files. It reuses
the real lexer/declaration/expression parsers, retaining token spans directly.
Empty/comment-only documents and valid single expressions return an empty list.
Library fragments need no main. Malformed/incomplete declarations fail atomically;
there is no partial-outline recovery yet. File commands retain the bounded
UTF-8 loader and parser/declaration budgets; errors go to stderr with nonzero
status and leave stdout empty.

This service performs no name resolution, prelude installation, type checking,
normalization, or execution. A syntactically complete but ill-typed declaration
can appear in the outline. Entries are declarations, not guessed semantic
function/type kinds. This is not an LSP, reference index, stable symbol identity,
cross-file navigation, or semantic rename. The supplied definition-name span is
a future navigation target, not resolution of references at cursor positions.

Module/import/export headers now use the [shared document parser](modules.md#parsing-progress).
Symbols and same-file navigation can inspect local declarations in these documents,
but imports/qualified references and filesystem identity are not resolved. Rename
previews conservatively reject module/import documents pending project checks.

## Same-file go-to-definition

~~~sh
./build/exec/fibril definition 12 12 examples/core/do-result.fib
~~~

The command takes one-based **scalar** line/column, then the source path.
Success returns a version-1 JSON object using the symbols command's coordinate
convention, with definition set to an exact target name span or null. A miss is
not an error. Invalid coordinates, decoding failures, and malformed syntax fail
with stderr diagnostics and empty stdout. CLI coordinates are decimal 1..65537,
consistent with the bounded file loader.

[Source.Navigation](../src/Fibril/Source/Navigation.idr) exposes definitionAt and
documentReferences over source Strings for unsaved-buffer integrations. Navigation
uses the parsed AST's scope structure plus original name-token spans, not a
textual search for declarations. Top-level references target the definition
header of an earlier declaration; signature names target their matching definition.
Parameters and local bindings target their own name token.

Scope matches the current nonrecursive frontend: types/values/actions of a
binding use the preceding environment, its body/subsequent statements use the
new binding, and nearest names shadow outer names. Pi/lambda binders, typed
lets, do result bindings, pure do lets, and block-result annotations are covered.
Wildcards, string/comment contents, punctuation, forward/self references without
an outer binding, and prelude names have no same-file target. Group parentheses
do not enlarge the clickable name range.

This is lexical navigation, not proof that an occurrence is well typed or has a
runtime permission. Complete but ill-typed source can still navigate. Malformed
documents fail atomically; no partial-error recovery is implemented. There are
no cross-file/prelude targets, stable symbol IDs, reference-at-project indexing,
rename edits, editor transport, or LSP UTF-16 conversion yet. Clients must use
the exact snapshot and convert coordinates before integrating with LSP.
Token lookup during scope traversal is bounded by source/parser limits but is
not optimized or a latency guarantee.

## Same-file references

~~~sh
./build/exec/fibril references 12 12 examples/core/do-result.fib
~~~

The references command uses the same one-based scalar coordinates and JSON
version as definition. Its references array contains exact name-token spans in
source order, **including declaration sites**. A top-level binding includes its
signature and definition headers; a local binding includes its binder token.
A miss produces an empty array. Errors leave stdout empty and go to stderr.

The pure referencesAt API groups entries by their resolved same-document target,
not by matching spelling. Thus a shadowing binder has a different result set,
a nonrecursive RHS may refer to an outer binder, and comments/string contents
are never included. Declarations still obey source order. This uses the current
lexical scope service, not type checking or prelude/project reference indexing.

The service accepts unsaved source Strings, but this command reads a bounded
file. The optional editor adapter below displays these results in a location
list. These ranges alone do not make a rename safe; the separate conservative
preview service below checks candidate scope changes.

## Capture-checked rename previews

~~~sh
./build/exec/fibril rename-preview 12 12 greetingText examples/core/do-result.fib
~~~

This produces version-1 JSON with edits, each containing an original-source range
and newText. It **does not write files**. All ranges use the same scalar coordinate
convention as navigation and refer to the original snapshot. Consumers applying
offset-based edits must use descending offset order or an equivalent simultaneous
edit operation; never apply them against an unrelated/stale buffer.

[Source.Rename](../src/Fibril/Source/Rename.idr) exposes the pure previewRename API.
It selects one same-file lexical target, proposes all of its declaration/use
edits, reparses the candidate, and compares every original resolved occurrence
and target after shifting their offsets. The resolved-reference count must also
stay unchanged, rejecting formerly unresolved/prelude names newly captured by
the renamed binder. Other shadowed groups are not edited.

The preview rejects malformed source, missing targets, duplicate declarations,
and changes in lexical resolution. The new name must be an ASCII identifier of
1..256 characters, not a keyword or underscore wildcard. Top-level main cannot
be renamed, nor can another top-level declaration be renamed to main; local names
do not acquire entry-point status. Same-name requests for ordinary bindings
return an empty edit list.

Both the input and the proposed result must fit 65,536 UTF-8 bytes. Replacement
length and offset shifting use scalar spans; unchanged Unicode strings/comments
and CRLF bytes are preserved. Size checks run before constructing an expanded
candidate. This is a prototype bound, not a time/allocation guarantee.

These checks use the current parser and lexical navigation model. They are not
a formal rename-correctness proof, type checking, or a project reference index.
Complete but ill-typed source may receive a preview. Prelude/cross-file targets,
imports/exports/API compatibility, editor rename application, file mutation, and
transactional application against versioned buffers remain unimplemented.
A fresh preview and review are still required before applying any edits.

## Navigation from Neovim/Vim

Build the compiler first, then configure its executable path:

~~~lua
vim.g.fibril_executable = "/absolute/path/to/fibril/build/exec/fibril"
~~~

For Vim, use let g:fibril_executable = '/absolute/path/to/fibril/build/exec/fibril'.
The default is fibril on PATH. This setting is a single trusted executable path,
not a shell command with arguments. No executable is discovered or installed
automatically from a project.

In a saved .fib buffer, place the cursor on a local reference and run:

~~~vim
:FibrilDefinition
~~~

The buffer-local definition command calls the compiler's definition service, validates the
version/coordinate convention and target bounds, converts UTF-8 byte cursor
columns to compiler scalar columns, then converts the returned target back to
editor bytes (including combining scalars). A successful jump preserves the
previous-context mark. No target or an error leaves the cursor unchanged.

[autoload/fibril.vim](../editors/vim/autoload/fibril.vim) contains the adapter.
It refuses modified/unnamed buffers, unsupported encodings/line endings, and
buffers differing from disk; it never saves source or writes temporary source
files. UTF-8 Unix and CRLF files are supported. The source file/buffer/window are
checked again after the request to avoid common stale-result jumps. This is not
a transaction against concurrent filesystem replacement.

Each shell argument is individually quoted for Vim/Neovim portability, including
paths with spaces/quotes. Compiler failures or malformed/unsupported JSON become
warnings rather than jumps. Calls are synchronous, manually invoked, and can
block the editor; there is no timeout, cancellation, or latency guarantee yet.

To display references, including declaration sites:

~~~vim
:FibrilReferences
~~~

This validates every returned range before creating a new window-local location
list and opening it. Press Enter on an item to navigate; use :lclose to close it.
Prior lists remain in location-list history (:lolder). Compiler errors, malformed
ranges, and misses leave the prior list intact. Source cursor position is not
changed before opening the list. Both commands share the same saved-buffer,
encoding, snapshot, compiler, and protocol checks.

Location-list results describe the queried snapshot, not a live reference index.
After source edits, save and re-run the query before relying on old results.

To review a rename, place the cursor on the binding or a local reference:

~~~vim
:FibrilRenamePreview greetingText
~~~

This invokes the compiler's capture-checked preview and opens a read-only,
nonmodifiable scratch diff. Only changed source lines are shown; source buffers
and files are never modified. Close it with :close. All edits are validated
before the window is created and applied only to an in-memory copy in descending
order. Multiple edits on one line and Unicode/CRLF source snapshots are supported.
A no-op, invalid/capturing name, stale/modified source, or malformed response does
not open a preview. This is review UI, not a patch-application command or formal
rename-correctness guarantee. Re-query after edits; previews are not live.

The runtime adds buffer-local <Plug>(FibrilDefinition), <Plug>(FibrilReferences),
and <Plug>(FibrilRenamePreview) mappings but does not override user/LazyVim keys.
The rename Plug mapping starts the command line for a name to be entered; it does
not apply changes. Optional Neovim setup: Optional Neovim setup:

~~~lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "fibril",
  callback = function()
    vim.keymap.set("n", "gd", "<Plug>(FibrilDefinition)", {
      buffer = true, remap = true, desc = "Fibril: same-file definition",
    })
    vim.keymap.set("n", "gr", "<Plug>(FibrilReferences)", {
      buffer = true, remap = true, desc = "Fibril: same-file references",
    })
  end,
})
~~~

The equivalent optional Vim setup is:

~~~vim
autocmd FileType fibril nmap <buffer> gd <Plug>(FibrilDefinition)
autocmd FileType fibril nmap <buffer> gr <Plug>(FibrilReferences)
~~~

You may additionally map a key to <Plug>(FibrilRenamePreview) if desired; no
rename key is assigned by default.

The ftplugin undo hook removes its commands and Plug mappings. User-created
gd/gr mappings remain the user's responsibility. The pure compiler APIs accept unsaved
Strings, but this file-based adapter deliberately does not yet support unsaved
buffers, outline UI, async jobs, or LSP transport.

## Tests and next work

~~~sh
make editor-test
~~~

This optional target requires Python 3 and at least one of Neovim/Vim on PATH.
It exercises every installed supported editor in a clean headless session, using
actual synID results rather than treating regex text as evidence of highlighting.
Current local validation uses Neovim 0.12.5 and Vim 9.1.

Tests cover strings/comments/escapes, quantities versus universe levels,
apostrophe/keyword boundaries, Unicode operators, declaration headers, incomplete
buffers, existing highlight/filetype preservation, reloads, and buffer-option undo.
When a local compiler is built, additional real-editor navigation tests check
Unicode/combining columns, Unix/CRLF snapshots, quoted paths, command/Plug setup,
no gd override, stale/modified refusal, missing compiler/malformed JSON, misses,
and command/mapping undo. Reference UI tests additionally check source cursor
preservation, byte-accurate list entries, location-window opening, and preserving
prior lists on misses/malformed or partially invalid responses. Those tests skip
when the compiler is absent. Checking tests validate located/unlocated errors,
UTF-8/combining/CRLF points, nonjumpable EOF/BOM/decoding cases, acceptance,
status/schema consistency, atomic handling of partially invalid diagnostics,
command/Plug cleanup, no source writes, and no program IO. Rename-preview tests additionally check read-only
scratch UI, multiple same-line edits without changing string data, unchanged
source buffers/cursors/files, no-op/keyword/modified-buffer refusal, and cleanup.
Editor columns in these tests are UTF-8 bytes, unlike compiler scalar positions.

Normal make test/build has no editor dependency. Future work is a grammar-backed
incremental highlighter and compiler-provided semantic tokens/symbol identities.
Project-wide references/rename, LSP UTF-16 conversion, and Tree-sitter-based
folding/selections remain unimplemented. Checked cross-file definition navigation
and read-only bundled Prelude references are implemented as described above.
