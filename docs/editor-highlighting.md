# Neovim and Vim highlighting and navigation

Status: implemented optional Vim-runtime package for the current Fibril subsets.
Includes optional compiler-backed same-file navigation. No Tree-sitter grammar,
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
2. Add the following, replacing the absolute path with your checkout location:

~~~lua
return {
  {
    name = "fibril-syntax",
    dir = "/absolute/path/to/fibril/editors/vim",
    lazy = false,
    config = function()
      vim.cmd("syntax enable")
      vim.cmd("runtime! ftdetect/fibril.vim")
    end,
  },
}
~~~

The dir must point to **editors/vim**, not the repository root. For this project's
usual local layout it might be `/Users/yourname/dev/idris2/projects/fibril/editors/vim`.
The directory must already exist; lazy.nvim loads these local files rather than
fetching a plugin. Keeping the checkout updated also updates the runtime files.

3. Restart Neovim and open `examples/core/hello-world.fib` from that checkout.
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
standard undo hook and optional FibrilDefinition command/Plug mapping. It does
not change indentation/formatting or override user keys such as gd.

[syntax/fibril.vim](../editors/vim/syntax/fibril.vim) contains only lexical rules.
Reload guards avoid duplicate setup. No editor code modifies core checking rules,
accepts proofs, or writes source files.

The [offline handbook](handbook.md#code-highlighting) also highlights Fibril and
Idris snippets/source pages. Its local Pandoc grammar is a separate presentation
layer, not this Vim runtime or a shared semantic language service.

## Parsed document symbols

The compiler now exposes a syntax-only declaration service:

~~~sh
./build/exec/fibril symbols examples/core/io-map.fib
./build/exec/fibril symbols stdlib/Prelude.fib
~~~

On success, stdout contains one JSON object with version 1, an explicit
coordinates label, and a symbols array in source order. Each symbol has name,
quantity ("0", "1", or "unrestricted"), range, selection, and definitionSelection.
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

The buffer-local command calls the compiler's definition service, validates the
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

The runtime adds a buffer-local <Plug>(FibrilDefinition) mapping but does not
override gd or LazyVim's mappings. Optional Neovim setup:

~~~lua
vim.api.nvim_create_autocmd("FileType", {
  pattern = "fibril",
  callback = function()
    vim.keymap.set("n", "gd", "<Plug>(FibrilDefinition)", {
      buffer = true, remap = true, desc = "Fibril: same-file definition",
    })
  end,
})
~~~

The equivalent optional Vim setup is:

~~~vim
autocmd FileType fibril nmap <buffer> gd <Plug>(FibrilDefinition)
~~~

The ftplugin undo hook removes its command and Plug mapping. User-created gd
mappings remain the user's responsibility. The pure compiler APIs accept unsaved
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
and command/mapping undo. Those tests skip when the compiler is absent.
Editor columns in these tests are UTF-8 bytes, unlike compiler scalar positions.

Normal make test/build has no editor dependency. Future work is a grammar-backed
incremental highlighter and compiler-provided semantic tokens/symbol identities.
Cross-file/prelude definitions, reference UI, project-wide rename, LSP UTF-16
conversion, and Tree-sitter-based folding/selections remain unimplemented.
