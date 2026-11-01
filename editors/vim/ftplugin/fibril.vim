" Minimal buffer settings; indentation and formatting are deliberately untouched.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

setlocal commentstring=--\ %s
setlocal comments=:--
setlocal iskeyword+=39

command! -buffer FibrilCheck call fibril#check()
nnoremap <buffer> <silent> <Plug>(FibrilCheck) :<C-U>FibrilCheck<CR>
command! -buffer FibrilDefinition call fibril#definition()
nnoremap <buffer> <silent> <Plug>(FibrilDefinition) :FibrilDefinition<CR>
command! -buffer -nargs=1 FibrilRenamePreview call fibril#rename_preview(<q-args>)
nnoremap <buffer> <silent> <Plug>(FibrilRenamePreview) :<C-U>FibrilRenamePreview<Space>
command! -buffer FibrilReferences call fibril#references()
nnoremap <buffer> <silent> <Plug>(FibrilReferences) :FibrilReferences<CR>

let b:undo_ftplugin = 'setlocal commentstring< comments< iskeyword<' .
      \ ' | silent! delcommand -buffer FibrilDefinition' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilDefinition)"' .
      \ ' | silent! delcommand -buffer FibrilReferences' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilReferences)"' .
      \ ' | silent! delcommand -buffer FibrilRenamePreview' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilRenamePreview)"' .
      \ ' | silent! delcommand -buffer FibrilCheck' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilCheck)"'
