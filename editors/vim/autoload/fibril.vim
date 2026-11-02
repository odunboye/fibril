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
    let protocol_version = index(['check-project', 'definition-project'], a:query) >= 0 ? 2 : 1
    let args = a:query ==# 'definition-project' ?
          \ [binary, 'definition', '--source-dir', a:1, '--entry', a:2, string(line('.')), string(scalar_column), path] :
          \ a:query ==# 'check-project' ? [binary, 'check', '--json', '--source-dir', a:1, path] :
          \ a:query ==# 'check' ? [binary, 'check', '--json', path] :
          \ [binary, a:query, string(line('.')), string(scalar_column)] + a:000 + [path]
    let field = a:query ==# 'definition-project' ? 'definition' : checking ? 'diagnostics' :
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
    return s:warn('no same-file definition at the cursor')
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

" Never load a dependency buffer just to obtain coordinates. Validate every
" available snapshot against disk and all aliases of already-loaded buffers.
function! s:project_contexts(result, root, entry) abort
  if type(get(a:result, 'entry', 0)) != v:t_string ||
        \ s:canonical(a:result.entry) !=# s:canonical(a:entry) ||
        \ !has_key(a:result, 'root') || type(get(a:result, 'sources', 0)) != v:t_list ||
        \ len(a:result.sources) > 32
    throw 'Invalid project identity or sources'
  endif
  if a:result.accepted && a:result.root is v:null
    throw 'Accepted project report omitted its canonical root'
  endif
  let root = s:canonical(a:root)
  if a:result.root isnot v:null &&
        \ (type(a:result.root) != v:t_string || a:result.root !=# root)
    throw 'Project root disagrees with the request'
  endif
  let prefix = root ==# '/' ? '/' : root . '/'
  let contexts = {}
  let bytes = 0
  let buffers = getbufinfo({'bufloaded': 1})
  for source in a:result.sources
    if type(source) != v:t_dict || type(get(source, 'path', 0)) != v:t_string ||
          \ type(get(source, 'text', 0)) != v:t_string ||
          \ has_key(contexts, source.path) || source.path !=# s:canonical(source.path) ||
          \ stridx(source.path, prefix) != 0 || strlen(source.text) > 65536
      throw 'Invalid project source snapshot'
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
  if (a:result.accepted || a:result.root isnot v:null) &&
        \ !has_key(contexts, s:canonical(a:entry))
    throw 'Complete project report omitted its entry snapshot'
  endif
  return contexts
endfunction

function! fibril#definition_project(root, entry) abort
  if type(a:root) != v:t_string || empty(a:root) ||
        \ type(a:entry) != v:t_string || empty(a:entry)
    return s:warn('configure a source root and project entry before project navigation')
  endif
  let response = s:request('definition-project', a:root, a:entry)
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
    let contexts = s:project_contexts(extend(copy(result), {'accepted': v:true}), a:root, a:entry)
    if !has_key(contexts, result.query)
      throw 'Query source snapshot omitted'
    endif
    let target = response.value
    if target is v:null
      return s:warn('no project definition at the cursor')
    endif
    if type(target) != v:t_dict || type(get(target, 'path', 0)) != v:t_string ||
          \ !has_key(contexts, target.path) || type(get(target, 'range', 0)) != v:t_dict ||
          \ type(get(target.range, 'start', 0)) != v:t_dict ||
          \ type(get(target.range, 'end', 0)) != v:t_dict
      throw 'Invalid project definition target'
    endif
    let context = contexts[target.path]
    let diagnostic = {'severity': 'error', 'stage': 'definition', 'message': '',
          \ 'byteOffset': v:null, 'position': target.range.start}
    let start = s:diagnostic_item(diagnostic, context)
    let diagnostic.position = target.range.end
    let finish = s:diagnostic_item(diagnostic, context)
    if target.range.start.line != target.range.end.line ||
          \ target.range.start.column >= target.range.end.column
      throw 'Invalid definition name range'
    endif
    if !context.bufnr || !start.valid || !finish.valid
      return s:warn('open the target in a UTF-8 buffer and retry project navigation: ' . target.path)
    endif
    let source_window = win_getid()
    normal! m'
    execute 'keepalt buffer ' . context.bufnr
    " Buffer-enter hooks are user configuration; never position using stale text.
    if win_getid() != source_window || bufnr('%') != context.bufnr ||
          \ s:canonical(expand('%:p')) !=# target.path || &modified ||
          \ index(['', 'utf-8'], &l:fileencoding) < 0 ||
          \ index(['unix', 'dos'], &l:fileformat) < 0 ||
          \ s:buffer_snapshot() !=# context.text || s:snapshot(target.path) !=# context.text
      return s:warn('target changed while entering its buffer; retry after saving')
    endif
    call cursor(start.lnum, start.col)
    return 1
  catch
    return s:warn('project definition refused: ' . v:exception)
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
