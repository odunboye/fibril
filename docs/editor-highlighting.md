# First Neovim and Vim highlighting

Status: implemented optional Vim-runtime package for the current Fibril subsets.
No Tree-sitter grammar, LSP server, semantic tokens, or symbol navigation is added.

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

## What it highlights

- Ordinary keywords: let/in, case/of, if/then/else.
- Builtin types and Boolean constructors.
- ASCII and Unicode lambda/arrows, annotations, and delimiters.
- Numbers, with contextual 0/1 quantity highlighting.
- Column-one declaration names, including quantity-prefixed headers.
- Console-profile IO and putStrLn spellings.
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

IO/putStrLn highlighting does not make those names available in ordinary core
terms; they only have builtin meaning in the restricted console profile.
Declaration highlighting does not infer whether a name denotes a function,
type, or value. Invalid source can still receive plausible colors.

## Buffer behavior and source

[ftdetect/fibril.vim](../editors/vim/ftdetect/fibril.vim) registers .fib files for
read/new-buffer events without replacing an already assigned filetype.

[ftplugin/fibril.vim](../editors/vim/ftplugin/fibril.vim) sets commentstring to
-- %s, line-comment metadata, and apostrophe-aware word motion. It supplies the
standard undo hook. It does not change indentation/formatting or add keybindings.

[syntax/fibril.vim](../editors/vim/syntax/fibril.vim) contains only lexical rules.
Reload guards avoid duplicate setup. No editor code modifies core checking rules,
accepts proofs, or writes source files.

The [offline handbook](handbook.md#code-highlighting) also highlights Fibril and
Idris snippets/source pages. Its local Pandoc grammar is a separate presentation
layer, not this Vim runtime or a shared semantic language service.

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
Editor columns in this test are UTF-8 bytes, unlike compiler scalar positions.

Normal make test/build has no editor dependency. Future work is a grammar-backed
incremental highlighter and compiler-provided semantic tokens/symbol identities.
Go-to-definition, references, project-wide rename, LSP UTF-16 conversion, and
Tree-sitter-based folding/selections remain unimplemented.
