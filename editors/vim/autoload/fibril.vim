" Optional synchronous compiler services. No automatic writes or key overrides.
function! s:warn(message) abort
  echohl WarningMsg
  echomsg 'Fibril: ' . a:message
  echohl None
  return 0
endfunction

function! s:snapshot(path) abort
  return join(readfile(a:path, 'b'), "\n")
endfunction

function! s:buffer_snapshot(...) abort
  let number = a:0 ? a:1 : bufnr('%')
  let lines = getbufline(number, 1, '$')
  if getfsize(bufname(number)) == 0 && lines ==# ['']
    return ''
  endif
  let text = join(lines, "\n")
  if getbufvar(number, '&endofline')
    let text .= "\n"
  endif
  if getbufvar(number, '&fileformat') ==# 'dos'
    let text = substitute(text, "\n", "\r\n", 'g')
  endif
  if getbufvar(number, '&bomb')
    let text = "\ufeff" . text
  endif
  return text
endfunction

" Buffer serialization for formatting does not depend on the saved file.
function! s:format_snapshot() abort
  let lines = getline(1, '$')
  for text in lines
    if stridx(text, "\n") >= 0
      throw 'buffer contains NUL data'
    endif
  endfor
  let text = join(lines, &l:fileformat ==# 'dos' ? "\r\n" : "\n")
  return text . (&l:endofline ? (&l:fileformat ==# 'dos' ? "\r\n" : "\n") : '')
endfunction

function! fibril#format() abort
  if &buftype !=# '' || !&modifiable || &readonly || &undolevels < 0
    return s:warn('formatting requires an editable normal buffer with undo enabled')
  endif
  if &encoding !=# 'utf-8' || index(['', 'utf-8'], &l:fileencoding) < 0 ||
        \ index(['unix', 'dos'], &l:fileformat) < 0 || &l:bomb
    return s:warn('formatting requires UTF-8 Unix/CRLF text without a BOM')
  endif
  let binary = get(g:, 'fibril_executable', 'fibril')
  if type(binary) != v:t_string || !executable(binary) ||
        \ !exists('*json_decode') || !exists('*byteidxcomp') || !exists('*setfperm')
    return s:warn('formatting requires the compiler, JSON/scalar conversion and private temporary-file support')
  endif
  let temporary = ''
  try
    let source = s:format_snapshot()
    if strlen(source) > 65536
      return s:warn('formatting source exceeds 65536 UTF-8 bytes')
    endif
    let number = bufnr('%')
    let window = win_getid()
    let name = expand('%:p')
    let tick = b:changedtick
    let options = [&l:fileformat, &l:endofline, &l:fileencoding, &l:bomb]
    let view = winsaveview()
    let scalar = strchars(strpart(getline('.'), 0, col('.') - 1))
    let temporary = tempname() . '.fib'
    if writefile([], temporary, 'b') != 0 || !setfperm(temporary, 'rw-------') ||
          \ writefile(split(source, "\n", 1), temporary, 'b') != 0
      throw 'could not prepare private formatting snapshot'
    endif
    let args = [binary, 'format', '--json', temporary]
    let output = system(join(map(args, 'shellescape(v:val)'), ' '))
    let status = v:shell_error
    if status
      return s:warn('format request failed: ' . strpart(output, 0, 512))
    endif
    if bufnr('%') != number || win_getid() != window || expand('%:p') !=# name ||
          \ b:changedtick != tick || s:format_snapshot() !=# source ||
          \ [&l:fileformat, &l:endofline, &l:fileencoding, &l:bomb] !=# options ||
          \ !&modifiable || &readonly || &buftype !=# '' || &undolevels < 0
      return s:warn('buffer changed during formatting; retry')
    endif
    let result = json_decode(output)
    if type(result) != v:t_dict || type(get(result, 'version', 0)) != v:t_number ||
          \ result.version != 1 ||
          \ get(result, 'coordinates', '') !=# 'unicode-scalars;offset=0;line=1;column=1' ||
          \ type(get(result, 'original', 0)) != v:t_string || result.original !=# source ||
          \ type(get(result, 'formatted', 0)) != v:t_string || strlen(result.formatted) > 65536
      throw 'invalid formatting response'
    endif
    if result.formatted ==# source
      return 1
    endif
    if substitute(result.formatted, '[ \t\r\n]', '', 'g') !=# substitute(source, '[ \t\r\n]', '', 'g')
      throw 'formatter changed non-whitespace content'
    endif
    let lines = split(result.formatted, "\n", 1)
    if options[1]
      if empty(lines) || lines[-1] !=# ''
        throw 'formatter changed final-newline presence'
      endif
      call remove(lines, -1)
    elseif result.formatted =~# "\n$"
      throw 'formatter added a final newline'
    endif
    if empty(lines)
      let lines = ['']
    endif
    if len(lines) < line('$')
      throw 'formatter removed physical lines'
    endif
    if options[0] ==# 'dos'
      for index in range(len(lines))
        if index < len(lines) - 1 || options[1]
          if lines[index] !~# "\r$"
            throw 'formatter changed CRLF line endings'
          endif
          let lines[index] = strpart(lines[index], 0, strlen(lines[index]) - 1)
        endif
      endfor
    endif
    if filter(copy(lines), 'v:val =~# "^[ \\t]*$"') !=# filter(getline(1, '$'), 'v:val =~# "^[ \\t]*$"')
      throw 'formatter changed blank lines'
    endif
    for index in range(len(lines))
      if matchstr(lines[index], "\r*$") !=# matchstr(getline(index + 1), "\r*$")
        throw 'formatter changed carriage-return content'
      endif
    endfor
    " Start a separate undo block without changing either global/local settings.
    let &g:undolevels = &g:undolevels
    if setline(1, lines) != 0
      throw 'could not update formatted buffer'
    endif
    let view.col = byteidxcomp(getline(view.lnum), min([scalar, strchars(getline(view.lnum))]))
    call winrestview(view)
    return 1
  catch
    return s:warn('formatting refused: ' . v:exception)
  finally
    if !empty(temporary)
      call delete(temporary)
    endif
  endtry
endfunction

function! s:request(query, ...) abort
  if &l:modified || empty(expand('%:p')) || !filereadable(expand('%:p'))
    return s:warn('save this buffer before requesting compiler services')
  endif
  if &encoding !=# 'utf-8' || index(['', 'utf-8'], &l:fileencoding) < 0 ||
        \ index(['unix', 'dos'], &l:fileformat) < 0
    return s:warn('compiler services require UTF-8 with Unix or CRLF line endings')
  endif
  if !exists('*json_decode') || !exists('*byteidxcomp')
    return s:warn('compiler services require JSON decoding and scalar/byte conversion support')
  endif
  let binary = get(g:, 'fibril_executable', 'fibril')
  if type(binary) != v:t_string || !executable(binary)
    return s:warn('compiler not executable; set g:fibril_executable to its path')
  endif
  let path = expand('%:p')
  let tick = b:changedtick
  let buffer_number = bufnr('%')
  let window = win_getid()
  if getfsize(path) > 65536
    return s:warn('source exceeds the compiler file limit of 65536 bytes')
  endif
  try
    let snapshot = s:snapshot(path)
    " Vim's empty-file buffer contains one empty line without file content.
    let buffer = getfsize(path) == 0 && line('$') == 1 && getline(1) ==# ''
          \ ? '' : s:buffer_snapshot()
    if snapshot !=# buffer
      return s:warn('buffer differs from disk; reload or save it before requesting compiler services')
    endif
    let scalar_column = strchars(strpart(getline('.'), 0, col('.') - 1)) + 1
    let checking = index(['check', 'check-project'], a:query) >= 0
    let protocol_version = index(['check-project', 'definition-project', 'definition-package'], a:query) >= 0 ? 2 : 1
    let args = a:query ==# 'definition-project' ?
          \ [binary, 'definition', '--source-dir', a:1, '--entry', a:2, string(line('.')), string(scalar_column), path] :
          \ a:query ==# 'definition-package' ? [binary, 'definition', '--package', a:1, string(line('.')), string(scalar_column), path] :
          \ a:query ==# 'check-project' ? [binary, 'check', '--json', '--source-dir', a:1, path] :
          \ a:query ==# 'check' ? [binary, 'check', '--json', path] :
          \ [binary, a:query, string(line('.')), string(scalar_column)] + a:000 + [path]
    let field = index(['definition-project', 'definition-package'], a:query) >= 0 ? 'definition' : checking ? 'diagnostics' :
          \ (a:query ==# 'rename-preview' ? 'edits' : a:query)
    " String-form system() is portable across Vim and Neovim. Quote each argument;
    " the configuration is an executable path, never a shell command fragment.
    let output = system(join(map(args, 'shellescape(v:val)'), ' '))
    let status = v:shell_error
    if status && !(checking && status == 1)
      return s:warn(a:query . ' request failed: ' . strpart(output, 0, 512))
    endif
    if bufnr('%') != buffer_number || win_getid() != window || expand('%:p') !=# path ||
          \ b:changedtick != tick || &l:modified || s:snapshot(path) !=# snapshot
      return s:warn('source changed during the request; retry after saving')
    endif
    let result = json_decode(output)
    if type(result) != v:t_dict || type(get(result, 'version', 0)) != v:t_number ||
          \ get(result, 'version', 0) != protocol_version ||
          \ get(result, 'coordinates', '') !=# 'unicode-scalars;offset=0;line=1;column=1' ||
          \ !has_key(result, field)
      return s:warn('unsupported ' . a:query . ' response')
    endif
    return {'value': result[field], 'path': path, 'result': result, 'status': status}
  catch
    return s:warn(a:query . ' request could not be read or decoded')
  endtry
endfunction

" Convert only validated, single-line name spans. Build all items before changing UI.
function! s:location(target) abort
  let target = a:target
  if type(target) != v:t_dict || type(get(target, 'start', 0)) != v:t_dict ||
        \ type(get(target, 'end', 0)) != v:t_dict
    throw 'Invalid navigation range'
  endif
  let row = get(target.start, 'line', 0)
  let column = get(target.start, 'column', 0)
  let finish = get(target.end, 'column', 0)
  if type(row) != v:t_number || type(column) != v:t_number || type(finish) != v:t_number ||
        \ row < 1 || row > line('$') || column < 1 || finish <= column ||
        \ get(target.end, 'line', 0) != row || finish > strchars(getline(row)) + 1
    throw 'Navigation range is outside the saved buffer'
  endif
  let byte_column = byteidxcomp(getline(row), column - 1) + 1
  let end_column = byteidxcomp(getline(row), finish - 1)
  if byte_column < 1 || end_column < byte_column
    throw 'Invalid scalar column in navigation range'
  endif
  return {'bufnr': bufnr('%'), 'lnum': row, 'col': byte_column,
        \ 'end_lnum': row, 'end_col': end_column, 'text': getline(row)}
endfunction

function! fibril#definition() abort
  let response = s:request('definition')
  if empty(response)
    return 0
  endif
  if response.value is v:null
    return fibril#reference()
  endif
  try
    let item = s:location(response.value)
    normal! m'
    call cursor(item.lnum, item.col)
    return 1
  catch
    return s:warn('invalid definition range')
  endtry
endfunction

function! fibril#references() abort
  let response = s:request('references')
  if empty(response)
    return 0
  endif
  if type(response.value) != v:t_list
    return s:warn('invalid references response')
  endif
  if empty(response.value)
    return s:warn('no same-file references at the cursor')
  endif
  try
    let items = []
    for target in response.value
      call add(items, s:location(target))
    endfor
    if setloclist(0, [], ' ', {'title': 'Fibril references (including declarations)',
          \ 'items': items}) != 0
      return s:warn('could not create reference location list')
    endif
    lopen
    return 1
  catch
    return s:warn('invalid references response or unavailable location window')
  endtry
endfunction

function! fibril#rename_preview(name) abort
  let response = s:request('rename-preview', a:name)
  if empty(response)
    return 0
  endif
  if type(response.value) != v:t_list
    return s:warn('invalid rename preview response')
  endif
  if empty(response.value)
    return s:warn('rename preview has no changes')
  endif
  try
    let original = getline(1, '$')
    let proposed = copy(original)
    let edits = []
    let previous_row = 0
    let previous_end = 0
    for edit in response.value
      if type(edit) != v:t_dict || type(get(edit, 'newText', 0)) != v:t_string ||
            \ edit.newText !=# a:name ||
            \ type(get(edit, 'range', 0)) != v:t_dict ||
            \ a:name !~# "^[A-Za-z_][A-Za-z0-9_']*$" || strlen(a:name) > 256 || a:name ==# '_'
        return s:warn('invalid rename preview edit')
      endif
      let item = s:location(edit.range)
      if item.lnum < previous_row || (item.lnum == previous_row && item.col <= previous_end)
        return s:warn('rename preview edits overlap or are not in source order')
      endif
      let previous_row = item.lnum
      let previous_end = item.end_col
      call add(edits, item)
    endfor
    " Every range refers to the original snapshot. Apply descending byte positions
    " to an in-memory copy only, never to the source buffer.
    for item in reverse(edits)
      let text = proposed[item.lnum - 1]
      let proposed[item.lnum - 1] = strpart(text, 0, item.col - 1) . a:name .
            \ strpart(text, item.end_col)
    endfor
    let lines = ['Fibril rename preview — source unchanged',
          \ 'Source: ' . strtrans(response.path),
          \ 'Review only; close this window with :close.', '',
          \ '--- original', '+++ proposed']
    for index in range(len(original))
      if original[index] !=# proposed[index]
        call extend(lines, ['@@ -' . (index + 1) . ' +' . (index + 1) . ' @@',
              \ '-' . original[index], '+' . proposed[index]])
      endif
    endfor
    let s:preview_number = get(s:, 'preview_number', 0) + 1
    new
    setlocal buftype=nofile bufhidden=wipe noswapfile nomodeline
    execute 'file ' . fnameescape('[Fibril rename preview ' . s:preview_number . ']')
    call setline(1, lines)
    setlocal filetype=diff nomodified readonly nomodifiable
    return 1
  catch
    return s:warn('invalid rename preview or unavailable preview window')
  endtry
endfunction

" Points may be at EOF, and core/decoding errors may have no scalar point at all.
" Such entries are deliberately nonjumpable rather than fabricated at line one.
function! s:diagnostic_item(diagnostic, ...) abort
  let context = a:0 ? a:1 : {'bufnr': bufnr('%'), 'lines': getline(1, '$'),
        \ 'ff': &l:fileformat, 'bomb': &l:bomb, 'eol': &l:endofline, 'validate': 1,
        \ 'reason': ''}
  let diagnostic = a:diagnostic
  if type(diagnostic) != v:t_dict || type(get(diagnostic, 'severity', 0)) != v:t_string ||
        \ diagnostic.severity !=# 'error' ||
        \ type(get(diagnostic, 'message', 0)) != v:t_string ||
        \ type(get(diagnostic, 'stage', 0)) != v:t_string ||
        \ !has_key(diagnostic, 'position') || !has_key(diagnostic, 'byteOffset')
    throw 'Invalid check diagnostic'
  endif
  let point = diagnostic.position
  let byte = diagnostic.byteOffset
  let label = '[' . diagnostic.stage . '] '
  let item = {'bufnr': context.bufnr, 'lnum': 0, 'col': 0, 'valid': 0, 'type': 'E'}
  if byte isnot v:null
    if point isnot v:null || type(byte) != v:t_number || byte < 0 || byte > 65536
      throw 'Invalid decoding byte offset'
    endif
    let label .= '[byte offset ' . byte . '; no scalar location] '
  elseif point is v:null
    let label .= '[unlocated] '
  else
    if type(point) != v:t_dict
      throw 'Invalid diagnostic point'
    endif
    let row = get(point, 'line', 0)
    let column = get(point, 'column', 0)
    let offset = get(point, 'offset', -1)
    if type(row) != v:t_number || type(column) != v:t_number || type(offset) != v:t_number ||
          \ row < 1 || row > 65537 || column < 1 || column > 65537 || offset < 0 || offset > 65536
      throw 'Invalid diagnostic coordinates'
    endif
    if !context.validate
      let label .= '[source ' . row . ':' . column . '; ' . context.reason . '] '
    elseif row == len(context.lines) + 1 && column == 1 && context.eol
      let label .= '[source ' . row . ':1; EOF has no buffer line] '
    elseif row > len(context.lines) || column > strchars(context.lines[row - 1]) + 1
      throw 'Diagnostic point is outside the saved source'
    elseif context.bomb
      let label .= '[source ' . row . ':' . column . '; hidden byte-order mark] '
    elseif !context.bufnr
      let label .= '[source ' . row . ':' . column . '; ' . context.reason . '] '
    else
      let item.lnum = row
      let item.col = byteidxcomp(context.lines[row - 1], column - 1) + 1
      let item.valid = 1
    endif
    if context.validate && !context.bomb
      let expected_offset = column - 1
      if row > 1
        for text in context.lines[:row - 2]
          let expected_offset += strchars(text) + (context.ff ==# 'dos' ? 2 : 1)
        endfor
      endif
      if offset != expected_offset
        throw 'Diagnostic offset disagrees with its scalar line/column'
      endif
    endif
  endif
  let item.text = label . diagnostic.message
  return item
endfunction

" Canonical identity is checked independently of the diagnostic's display path.
function! s:canonical(path) abort
  let path = resolve(fnamemodify(a:path, ':p'))
  return path ==# '/' ? path : substitute(path, '/\+$', '', '')
endfunction

function! s:source_context(text) abort
  let context = {'bufnr': 0, 'bomb': 0, 'validate': 1, 'eol': 0, 'ff': 'unix',
        \ 'lines': [''], 'reason': 'open source and rerun project check'}
  let remainder = substitute(a:text, "\r\n", '', 'g')
  if stridx(remainder, "\r") >= 0 ||
        \ (stridx(a:text, "\r\n") >= 0 && stridx(remainder, "\n") >= 0) ||
        \ strpart(a:text, 0, 3) ==# "\ufeff"
    let context.validate = 0
    let context.reason = 'unsupported line endings or hidden byte-order mark'
    return context
  endif
  let context.ff = stridx(a:text, "\r\n") >= 0 ? 'dos' : 'unix'
  let text = substitute(a:text, "\r\n", "\n", 'g')
  let context.lines = split(text, "\n", 1)
  let context.eol = !empty(text) && strpart(text, strlen(text) - 1) ==# "\n"
  if context.eol
    call remove(context.lines, -1)
  endif
  if empty(context.lines)
    let context.lines = ['']
  endif
  return context
endfunction

" Decode manifest metadata independently instead of trusting report fields alone.
function! s:validate_manifest_report(manifest, module_prefix) abort
  let binary = get(g:, 'fibril_executable', 'fibril')
  let output = system(join(map([binary, 'manifest', a:manifest.path], 'shellescape(v:val)'), ' '))
  if v:shell_error
    throw 'Package manifest inspection failed'
  endif
  let report = json_decode(output)
  if type(report) != v:t_dict || get(report, 'version', 0) != 1 ||
        \ get(report, 'kind', '') !=# 'manifest-inspection' ||
        \ type(get(report, 'path', 0)) != v:t_string || s:canonical(report.path) !=# a:manifest.path ||
        \ get(report, 'name', '') !=# a:manifest.name ||
        \ get(report, 'module_prefix', '') !=# a:module_prefix ||
        \ get(report, 'source_dir', '') !=# a:manifest.source_dir ||
        \ get(report, 'dependencies', 0) !=# a:manifest.dependencies ||
        \ s:snapshot(a:manifest.path) !=# a:manifest.text
    throw 'Package manifest inspection disagrees with checked metadata'
  endif
endfunction

" Validate all checked package manifests as well as the source-root inventory.
function! s:package_roots(result, manifest) abort
  let scope = get(a:result, 'package_scope', 0)
  let manifests = get(a:result, 'manifests', 0)
  if type(get(a:result, 'manifest', 0)) != v:t_string ||
        \ a:result.manifest !=# s:canonical(a:manifest) ||
        \ type(scope) != v:t_dict || type(get(scope, 'entry_package', 0)) != v:t_string ||
        \ type(get(scope, 'inventory', 0)) != v:t_list || empty(scope.inventory) ||
        \ len(scope.inventory) > 64 || type(manifests) != v:t_list ||
        \ len(manifests) != len(scope.inventory)
    throw 'Invalid package identity or inventory'
  endif
  let roots = {}
  let dependency_names = {}
  let module_prefixes = {}
  for item in scope.inventory
    if type(item) != v:t_dict || type(get(item, 'name', 0)) != v:t_string ||
          \ empty(item.name) || has_key(roots, item.name) ||
          \ type(get(item, 'source_root', 0)) != v:t_string ||
          \ item.source_root !=# s:canonical(item.source_root) || !isdirectory(item.source_root) ||
          \ type(get(item, 'module_prefix', 0)) != v:t_string || empty(item.module_prefix) ||
          \ type(get(item, 'dependencies', 0)) != v:t_list
      throw 'Invalid package source root'
    endif
    for dependency in item.dependencies
      if type(dependency) != v:t_string || empty(dependency)
        throw 'Invalid package dependency identity'
      endif
    endfor
    let roots[item.name] = item.source_root
    let dependency_names[item.name] = item.dependencies
    let module_prefixes[item.name] = item.module_prefix
  endfor
  if !has_key(roots, scope.entry_package) || get(a:result, 'root', '') !=# roots[scope.entry_package]
    throw 'Package root disagrees with checked inventory'
  endif
  let seen = {}
  let paths = {}
  let edges = {}
  let parents = {}
  for manifest in manifests
    if type(manifest) != v:t_dict || type(get(manifest, 'name', 0)) != v:t_string ||
          \ !has_key(roots, manifest.name) || has_key(seen, manifest.name) ||
          \ type(get(manifest, 'path', 0)) != v:t_string || has_key(paths, manifest.path) ||
          \ manifest.path !=# s:canonical(manifest.path) ||
          \ type(get(manifest, 'text', 0)) != v:t_string || strlen(manifest.text) > 8192 ||
          \ type(get(manifest, 'source_dir', 0)) != v:t_string || empty(manifest.source_dir) ||
          \ manifest.source_dir =~# '^/' || type(get(manifest, 'dependencies', 0)) != v:t_list ||
          \ !filereadable(manifest.path) || getfsize(manifest.path) > 8192 ||
          \ s:snapshot(manifest.path) !=# manifest.text
      throw 'Package manifest changed or is invalid'
    endif
    let package_root = s:canonical(fnamemodify(manifest.path, ':h'))
    let package_prefix = package_root ==# '/' ? '/' : package_root . '/'
    if fnamemodify(manifest.path, ':t') !=# 'fibril.yaml' ||
          \ (roots[manifest.name] !=# package_root && stridx(roots[manifest.name], package_prefix) != 0)
      throw 'Package source root is outside its manifest directory'
    endif
    let declared_root = package_root . '/' . manifest.source_dir
    if !isdirectory(declared_root) || s:canonical(declared_root) !=# roots[manifest.name]
      throw 'Package source directory no longer resolves to its checked root'
    endif
    let dep_names = []
    for dependency in manifest.dependencies
      if type(dependency) != v:t_dict || type(get(dependency, 'name', 0)) != v:t_string ||
            \ empty(dependency.name) || index(dep_names, dependency.name) >= 0 ||
            \ type(get(dependency, 'path', 0)) != v:t_string || empty(dependency.path) ||
            \ dependency.path =~# '^/'
        throw 'Invalid package dependency path'
      endif
      call add(dep_names, dependency.name)
    endfor
    if sort(copy(dep_names)) !=# sort(copy(dependency_names[manifest.name]))
      throw 'Package dependency metadata disagrees with checked inventory'
    endif
    call s:validate_manifest_report(manifest, module_prefixes[manifest.name])
    for buffer in getbufinfo({'bufloaded': 1})
      if !empty(buffer.name) && s:canonical(buffer.name) ==# manifest.path &&
            \ (getbufvar(buffer.bufnr, '&modified') || s:buffer_snapshot(buffer.bufnr) !=# manifest.text)
        throw 'Package manifest buffer is modified or differs from disk'
      endif
    endfor
    let seen[manifest.name] = manifest.path
    let paths[manifest.path] = 1
    let edges[manifest.name] = manifest.dependencies
    let parents[manifest.name] = package_root
  endfor
  for [name, dependencies] in items(edges)
    for dependency in dependencies
      let target = parents[name] . '/' . dependency.path . '/fibril.yaml'
      if !filereadable(target) || !has_key(seen, dependency.name) ||
            \ s:canonical(target) !=# seen[dependency.name]
        throw 'Package dependency path no longer resolves to its checked manifest'
      endif
    endfor
  endfor
  if get(seen, scope.entry_package, '') !=# s:canonical(a:manifest)
    throw 'Package manifest does not own the checked entry'
  endif
  return roots
endfunction

" Re-resolve and check every component, as the checked module loader does.
function! s:package_module_path(root, module) abort
  if !exists('*readdir')
    throw 'Package navigation requires directory inspection support'
  endif
  let pieces = split(a:module, '\.')
  let directory = a:root
  let prefix = a:root ==# '/' ? '/' : a:root . '/'
  for index in range(len(pieces))
    let component = pieces[index] . (index == len(pieces) - 1 ? '.fib' : '')
    if index(readdir(directory), component) < 0
      throw 'Package module path no longer resolves with its checked spelling'
    endif
    let candidate = directory . '/' . component
    if index == len(pieces) - 1 ? !filereadable(candidate) : !isdirectory(candidate)
      throw 'Package module path no longer resolves to its checked source'
    endif
    let directory = s:canonical(candidate)
    if directory !=# a:root && stridx(directory, prefix) != 0
      throw 'Package module path no longer resolves within its checked root'
    endif
  endfor
  return directory
endfunction

" Re-resolve module names as well as canonical snapshots: a path symlink can
" change while the previously resolved source file itself remains unchanged.
function! s:package_module_paths(result, roots, contexts) abort
  let modules = get(a:result, 'module_resolutions', 0)
  if type(modules) != v:t_list || len(modules) != len(a:contexts)
    throw 'Invalid package module resolutions'
  endif
  let seen = {}
  for module in modules
    if type(module) != v:t_dict || type(get(module, 'path', 0)) != v:t_string ||
          \ !has_key(a:contexts, module.path) || has_key(seen, module.path) ||
          \ type(get(module, 'source_root', 0)) != v:t_string ||
          \ index(values(a:roots), module.source_root) < 0 ||
          \ type(get(module, 'module', 0)) != v:t_string ||
          \ module.module !~# '^[A-Z][A-Za-z0-9_]*\(\.[A-Z][A-Za-z0-9_]*\)*$' ||
          \ len(split(module.module, '\.')) > 16
      throw 'Invalid package module identity'
    endif
    if s:package_module_path(module.source_root, module.module) !=# module.path
      throw 'Package module path no longer resolves to its checked source'
    endif
    let seen[module.path] = 1
  endfor
endfunction

" Never load a dependency buffer just to obtain coordinates. Validate every
" available snapshot against disk and all aliases of already-loaded buffers.
function! s:project_contexts(result, root, entry, ...) abort
  let manifest = a:0 ? a:1 : ''
  if type(get(a:result, 'entry', 0)) != v:t_string ||
        \ !has_key(a:result, 'root') || type(get(a:result, 'sources', 0)) != v:t_list ||
        \ len(a:result.sources) > 32
    throw 'Invalid project identity or sources'
  endif
  if a:result.accepted && a:result.root is v:null
    throw 'Accepted project report omitted its canonical root'
  endif
  if empty(manifest)
    if s:canonical(a:result.entry) !=# s:canonical(a:entry)
      throw 'Project entry disagrees with the request'
    endif
    let root = s:canonical(a:root)
    if a:result.root isnot v:null &&
          \ (type(a:result.root) != v:t_string || a:result.root !=# root)
      throw 'Project root disagrees with the request'
    endif
    let roots = {'single': root}
  else
    let roots = s:package_roots(a:result, manifest)
  endif
  let contexts = {}
  let bytes = 0
  let buffers = getbufinfo({'bufloaded': 1})
  for source in a:result.sources
    if type(source) != v:t_dict || type(get(source, 'path', 0)) != v:t_string ||
          \ type(get(source, 'text', 0)) != v:t_string ||
          \ has_key(contexts, source.path) || source.path !=# s:canonical(source.path) ||
          \ strlen(source.text) > 65536
      throw 'Invalid project source snapshot'
    endif
    let matches = 0
    for root in values(roots)
      let prefix = root ==# '/' ? '/' : root . '/'
      if stridx(source.path, prefix) == 0
        let matches += 1
      endif
    endfor
    if matches != 1
      throw 'Project source is outside or ambiguously within checked roots'
    endif
    let bytes += strlen(source.text)
    if bytes > 524288 || !filereadable(source.path) || getfsize(source.path) > 65536 ||
          \ s:snapshot(source.path) !=# source.text
      throw 'Project source changed on disk'
    endif
    let context = s:source_context(source.text)
    let context.text = source.text
    for buffer in buffers
      if !empty(buffer.name) && s:canonical(buffer.name) ==# source.path
        if getbufvar(buffer.bufnr, '&modified') ||
              \ index(['', 'utf-8'], getbufvar(buffer.bufnr, '&fileencoding')) < 0 ||
              \ index(['unix', 'dos'], getbufvar(buffer.bufnr, '&fileformat')) < 0 ||
              \ s:buffer_snapshot(buffer.bufnr) !=# source.text
          throw 'Project buffer is modified, differently encoded, or differs from disk'
        endif
        let context.bufnr = buffer.bufnr
      endif
    endfor
    let contexts[source.path] = context
  endfor
  if !empty(manifest)
    call s:package_module_paths(a:result, roots, contexts)
  endif
  let expected_entry = empty(manifest) ? a:entry : a:result.entry
  if !empty(expected_entry) && (a:result.accepted || a:result.root isnot v:null) &&
        \ !has_key(contexts, s:canonical(expected_entry))
    throw 'Complete project report omitted its entry snapshot'
  endif
  return contexts
endfunction

" Validate coordinates against source text without requiring a loaded buffer.
function! s:definition_position(point, context) abort
  if !a:context.validate || a:context.bomb || type(a:point) != v:t_dict
    throw 'Unsupported definition source representation'
  endif
  let row = get(a:point, 'line', 0)
  let column = get(a:point, 'column', 0)
  let offset = get(a:point, 'offset', -1)
  if type(row) != v:t_number || type(column) != v:t_number ||
        \ type(offset) != v:t_number || row < 1 || row > len(a:context.lines) ||
        \ column < 1 || column > strchars(a:context.lines[row - 1]) + 1 ||
        \ offset < 0 || offset > 65536
    throw 'Definition point is outside its source snapshot'
  endif
  let expected = column - 1
  if row > 1
    for text in a:context.lines[:row - 2]
      let expected += strchars(text) + (a:context.ff ==# 'dos' ? 2 : 1)
    endfor
  endif
  if offset != expected
    throw 'Definition offset disagrees with its scalar line/column'
  endif
  return [row, byteidxcomp(a:context.lines[row - 1], column - 1) + 1]
endfunction

function! s:project_definition(query, root, entry, manifest) abort
  let response = a:query ==# 'definition-package' ?
        \ s:request(a:query, a:manifest) : s:request(a:query, a:root, a:entry)
  if empty(response)
    return 0
  endif
  try
    let result = response.result
    if type(get(result, 'checked', 0)) != v:t_bool || !result.checked ||
          \ type(get(result, 'query', 0)) != v:t_string ||
          \ result.query !=# s:canonical(response.path)
      throw 'Invalid project definition identity'
    endif
    let contexts = s:project_contexts(extend(copy(result), {'accepted': v:true}), a:root, a:entry, a:manifest)
    if !has_key(contexts, result.query)
      throw 'Query source snapshot omitted'
    endif
    let target = response.value
    if target is v:null
      return fibril#reference()
    endif
    if type(target) != v:t_dict || type(get(target, 'path', 0)) != v:t_string ||
          \ !has_key(contexts, target.path) || type(get(target, 'range', 0)) != v:t_dict ||
          \ type(get(target.range, 'start', 0)) != v:t_dict ||
          \ type(get(target.range, 'end', 0)) != v:t_dict
      throw 'Invalid project definition target'
    endif
    let context = contexts[target.path]
    let start = s:definition_position(target.range.start, context)
    call s:definition_position(target.range.end, context)
    if target.range.start.line != target.range.end.line ||
          \ target.range.start.column >= target.range.end.column
      throw 'Invalid definition name range'
    endif
    let source_window = win_getid()
    normal! m'
    if context.bufnr
      execute 'keepalt buffer ' . context.bufnr
    else
      execute 'keepalt edit ++enc=utf-8 ' . fnameescape(target.path)
    endif
    " Buffer-enter hooks are user configuration; never position using stale text.
    if win_getid() != source_window ||
          \ s:canonical(expand('%:p')) !=# target.path || &modified ||
          \ index(['', 'utf-8'], &l:fileencoding) < 0 ||
          \ index(['unix', 'dos'], &l:fileformat) < 0 ||
          \ s:buffer_snapshot() !=# context.text || s:snapshot(target.path) !=# context.text
      return s:warn('target changed while entering its buffer; retry after saving')
    endif
    " Revalidate the whole project after read/enter hooks, not only the target.
    call s:project_contexts(extend(copy(result), {'accepted': v:true}), a:root, a:entry, a:manifest)
    call cursor(start[0], start[1])
    return 1
  catch
    return s:warn('project definition refused: ' . v:exception)
  endtry
endfunction

function! fibril#definition_project(root, entry) abort
  if type(a:root) != v:t_string || empty(a:root) ||
        \ type(a:entry) != v:t_string || empty(a:entry)
    return s:warn('configure a source root and project entry before project navigation')
  endif
  return s:project_definition('definition-project', a:root, a:entry, '')
endfunction

function! fibril#definition_package(manifest) abort
  if type(a:manifest) != v:t_string || empty(a:manifest) || !filereadable(a:manifest)
    return s:warn('configure a readable package manifest before package navigation')
  endif
  return s:project_definition('definition-package', '', '', a:manifest)
endfunction

" Display compiled reference data, never a guessed filesystem definition.
function! fibril#reference() abort
  let response = s:request('reference')
  if empty(response)
    return 0
  endif
  try
    let target = response.value
    if target is v:null
      return s:warn('no built-in or Prelude reference at the cursor')
    endif
    if type(target) != v:t_dict || type(get(target, 'name', 0)) != v:t_string ||
          \ empty(target.name) || strlen(target.name) > 256
      throw 'Invalid reference identity'
    endif
    let kind = get(target, 'kind', '')
    let position = [1, 1]
    if kind ==# 'builtin-documentation'
      let lines = get(target, 'lines', 0)
      if type(lines) != v:t_list || empty(lines) || len(lines) > 64
        throw 'Invalid built-in reference'
      endif
      for text in lines
        if type(text) != v:t_string || strlen(text) > 4096 || stridx(text, "\n") >= 0
          throw 'Invalid reference line'
        endif
      endfor
      let lines = ['Built-in reference: ' . target.name, '(documentation, not a source declaration)', ''] + lines
      let title = 'Fibril reference: ' . target.name
    elseif kind ==# 'bundled-prelude-source'
      if type(get(target, 'source', 0)) != v:t_string || strlen(target.source) > 65536 ||
            \ type(get(target, 'range', 0)) != v:t_dict
        throw 'Invalid Prelude snapshot'
      endif
      let context = s:source_context(target.source)
      let position = s:definition_position(get(target.range, 'start', 0), context)
      call s:definition_position(get(target.range, 'end', 0), context)
      if target.range.start.line != target.range.end.line ||
            \ target.range.start.column >= target.range.end.column
        throw 'Invalid Prelude name range'
      endif
      let lines = context.lines
      let title = 'Fibril Prelude (bundled source snapshot)'
    else
      throw 'Unsupported reference kind'
    endif
    botright vnew
    setlocal buftype=nofile bufhidden=wipe noswapfile nomodeline
    execute 'file ' . fnameescape(title . ' #' . bufnr('%'))
    call setline(1, lines)
    if kind ==# 'bundled-prelude-source'
      setlocal filetype=fibril
    else
      setlocal filetype=text
    endif
    setlocal nomodifiable readonly nomodified
    call cursor(position[0], position[1])
    return 1
  catch
    return s:warn('reference refused: ' . v:exception)
  endtry
endfunction

function! fibril#check_project(root) abort
  if type(a:root) != v:t_string || empty(a:root)
    return s:warn('set b:fibril_source_dir or g:fibril_source_dir before project checking')
  endif
  let response = s:request('check-project', a:root)
  if empty(response)
    return 0
  endif
  try
    let result = response.result
    if type(get(result, 'accepted', 0)) != v:t_bool ||
          \ type(response.value) != v:t_list || type(get(result, 'report', 0)) != v:t_list ||
          \ (result.accepted && (response.status != 0 || !empty(response.value))) ||
          \ (!result.accepted && (response.status != 1 || empty(response.value) || !empty(result.report)))
      throw 'Inconsistent project check report'
    endif
    for message in result.report
      if type(message) != v:t_string
        throw 'Invalid project check information'
      endif
    endfor
    let contexts = s:project_contexts(result, a:root, response.path)
    let items = []
    for diagnostic in response.value
      if type(diagnostic) != v:t_dict || type(get(diagnostic, 'path', 0)) != v:t_string ||
            \ type(get(diagnostic, 'sourceAvailable', 0)) != v:t_bool
        throw 'Invalid diagnostic source identity'
      endif
      if diagnostic.sourceAvailable
        if !has_key(contexts, diagnostic.path)
          throw 'Diagnostic has no matching source snapshot'
        endif
        let context = contexts[diagnostic.path]
      else
        let context = {'bufnr': 0, 'validate': 0, 'reason': 'snapshot unavailable'}
      endif
      let item = s:diagnostic_item(diagnostic, context)
      let item.text = diagnostic.path . ': ' . item.text
      call add(items, item)
    endfor
    if setloclist(0, [], ' ', {'title': 'Fibril project check: ' .
          \ (result.accepted ? 'accepted' : 'rejected'), 'items': items}) != 0
      return s:warn('could not create project check location list')
    endif
    if result.accepted
      echomsg 'Fibril: ' . (empty(result.report) ? 'project checking accepted' :
            \ strpart(join(result.report, ' | '), 0, 512))
    else
      lopen
    endif
    return 1
  catch
    return s:warn('project check refused: ' . v:exception)
  endtry
endfunction

function! fibril#check() abort
  let response = s:request('check')
  if empty(response)
    return 0
  endif
  try
    let result = response.result
    if type(get(result, 'accepted', 0)) != v:t_bool ||
          \ type(response.value) != v:t_list || type(get(result, 'report', 0)) != v:t_list
      return s:warn('invalid check report')
    endif
    for message in result.report
      if type(message) != v:t_string
        return s:warn('invalid check information')
      endif
    endfor
    if result.accepted
      if response.status != 0 || !empty(response.value)
        return s:warn('inconsistent accepted check report')
      endif
      if setloclist(0, [], ' ', {'title': 'Fibril check: accepted', 'items': []}) != 0
        return s:warn('could not create check location list')
      endif
      echomsg 'Fibril: ' . (empty(result.report) ? 'runtime checking accepted' :
            \ strpart(join(result.report, ' | '), 0, 512))
      return 1
    endif
    if response.status != 1 || empty(response.value) || !empty(result.report)
      return s:warn('inconsistent rejected check report')
    endif
    let items = []
    for diagnostic in response.value
      call add(items, s:diagnostic_item(diagnostic))
    endfor
    if setloclist(0, [], ' ', {'title': 'Fibril check: rejected', 'items': items}) != 0
      return s:warn('could not create check location list')
    endif
    lopen
    return 1
  catch
    return s:warn('invalid check response or unavailable location window')
  endtry
endfunction
