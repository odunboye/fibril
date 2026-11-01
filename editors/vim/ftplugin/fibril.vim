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

let b:undo_ftplugin = 'setlocal commentstring< comments< iskeyword<' .
      \ ' | silent! delcommand -buffer FibrilDefinition' .
      \ ' | silent! nunmap <buffer> <Plug>(FibrilDefinition)'
