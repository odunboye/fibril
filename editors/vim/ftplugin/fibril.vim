" Minimal buffer settings; indentation and formatting are deliberately untouched.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

setlocal commentstring=--\ %s
setlocal comments=:--
setlocal iskeyword+=39

command! -buffer FibrilDefinition call fibril#definition()
nnoremap <buffer> <silent> <Plug>(FibrilDefinition) :FibrilDefinition<CR>
command! -buffer FibrilReferences call fibril#references()
nnoremap <buffer> <silent> <Plug>(FibrilReferences) :FibrilReferences<CR>

let b:undo_ftplugin = 'setlocal commentstring< comments< iskeyword<' .
      \ ' | silent! delcommand -buffer FibrilDefinition' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilDefinition)"' .
      \ ' | silent! delcommand -buffer FibrilReferences' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilReferences)"'
