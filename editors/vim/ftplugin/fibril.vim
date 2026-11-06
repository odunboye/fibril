" Minimal buffer settings; indentation and formatting are deliberately untouched.
if exists('b:did_ftplugin')
  finish
endif
let b:did_ftplugin = 1

setlocal commentstring=--\ %s
setlocal comments=:--
setlocal iskeyword+=39

command! -buffer FibrilFormat call fibril#format()
nnoremap <buffer> <silent> <Plug>(FibrilFormat) :<C-U>FibrilFormat<CR>
command! -buffer FibrilReference call fibril#reference()
nnoremap <buffer> <silent> <Plug>(FibrilReference) :<C-U>FibrilReference<CR>
command! -buffer FibrilCheckProject call fibril#check_project(get(b:, 'fibril_source_dir', get(g:, 'fibril_source_dir', '')))
nnoremap <buffer> <silent> <Plug>(FibrilCheckProject) :<C-U>FibrilCheckProject<CR>
command! -buffer FibrilCheck call fibril#check()
nnoremap <buffer> <silent> <Plug>(FibrilCheck) :<C-U>FibrilCheck<CR>
command! -buffer FibrilDefinitionProject call fibril#definition_project(get(b:, 'fibril_source_dir', get(g:, 'fibril_source_dir', '')), get(b:, 'fibril_project_entry', get(g:, 'fibril_project_entry', expand('%:p'))))
nnoremap <buffer> <silent> <Plug>(FibrilDefinitionProject) :<C-U>FibrilDefinitionProject<CR>
command! -buffer FibrilDefinitionPackage call fibril#definition_package(get(b:, 'fibril_package_manifest', get(g:, 'fibril_package_manifest', '')))
nnoremap <buffer> <silent> <Plug>(FibrilDefinitionPackage) :<C-U>FibrilDefinitionPackage<CR>
command! -buffer FibrilDefinition call fibril#definition()
nnoremap <buffer> <silent> <Plug>(FibrilDefinition) :FibrilDefinition<CR>
command! -buffer -nargs=1 FibrilRenamePreview call fibril#rename_preview(<q-args>)
nnoremap <buffer> <silent> <Plug>(FibrilRenamePreview) :<C-U>FibrilRenamePreview<Space>
command! -buffer FibrilReferences call fibril#references()
nnoremap <buffer> <silent> <Plug>(FibrilReferences) :FibrilReferences<CR>

let b:undo_ftplugin = 'setlocal commentstring< comments< iskeyword<' .
      \ ' | silent! delcommand -buffer FibrilFormat' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilFormat)"' .
      \ ' | silent! delcommand -buffer FibrilReference' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilReference)"' .
      \ ' | silent! delcommand -buffer FibrilDefinitionProject' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilDefinitionProject)"' .
      \ ' | silent! delcommand -buffer FibrilDefinitionPackage' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilDefinitionPackage)"' .
      \ ' | silent! delcommand -buffer FibrilCheckProject' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilCheckProject)"' .
      \ ' | silent! delcommand -buffer FibrilDefinition' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilDefinition)"' .
      \ ' | silent! delcommand -buffer FibrilReferences' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilReferences)"' .
      \ ' | silent! delcommand -buffer FibrilRenamePreview' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilRenamePreview)"' .
      \ ' | silent! delcommand -buffer FibrilCheck' .
      \ ' | execute "silent! nunmap <buffer> <Plug>(FibrilCheck)"'
