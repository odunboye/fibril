" Optional synchronous CLI navigation. No automatic writes or key overrides.
function! s:warn(message) abort
  echohl WarningMsg
  echomsg 'Fibril: ' . a:message
  echohl None
  return 0
endfunction

function! s:snapshot(path) abort
  return join(readfile(a:path, 'b'), "\n")
endfunction

function! s:buffer_snapshot() abort
  let text = join(getline(1, '$'), "\n")
  if &l:endofline
    let text .= "\n"
  endif
  if &l:fileformat ==# 'dos'
    let text = substitute(text, "\n", "\r\n", 'g')
  endif
  if &l:bomb
    let text = "\ufeff" . text
  endif
  return text
endfunction

function! fibril#definition() abort
  if &l:modified || empty(expand('%:p')) || !filereadable(expand('%:p'))
    return s:warn('save this buffer before requesting a definition')
  endif
  if &encoding !=# 'utf-8' || index(['', 'utf-8'], &l:fileencoding) < 0 ||
        \ index(['unix', 'dos'], &l:fileformat) < 0
    return s:warn('navigation requires UTF-8 with Unix or CRLF line endings')
  endif
  if !exists('*json_decode') || !exists('*byteidxcomp')
    return s:warn('navigation requires JSON decoding and scalar/byte conversion support')
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
      return s:warn('buffer differs from disk; reload or save it before navigation')
    endif
    let scalar_column = strchars(strpart(getline('.'), 0, col('.') - 1)) + 1
    let args = [binary, 'definition', string(line('.')), string(scalar_column), path]
    " String-form system() is portable across Vim and Neovim. Quote each argument;
    " the configuration is an executable path, never a shell command fragment.
    let output = system(join(map(args, 'shellescape(v:val)'), ' '))
    if v:shell_error
      return s:warn('definition request failed: ' . strpart(output, 0, 512))
    endif
    if bufnr('%') != buffer_number || win_getid() != window || expand('%:p') !=# path ||
          \ b:changedtick != tick || &l:modified || s:snapshot(path) !=# snapshot
      return s:warn('source changed during the request; retry after saving')
    endif
    let result = json_decode(output)
    if type(result) != v:t_dict || get(result, 'version', 0) != 1 ||
          \ get(result, 'coordinates', '') !=# 'unicode-scalars;offset=0;line=1;column=1' ||
          \ !has_key(result, 'definition')
      return s:warn('unsupported definition response')
    endif
    let target = result.definition
    if target is v:null
      return s:warn('no same-file definition at the cursor')
    endif
    if type(target) != v:t_dict || type(get(target, 'start', 0)) != v:t_dict ||
          \ type(get(target, 'end', 0)) != v:t_dict
      return s:warn('invalid definition range')
    endif
    let row = get(target.start, 'line', 0)
    let column = get(target.start, 'column', 0)
    let finish = get(target.end, 'column', 0)
    if type(row) != v:t_number || type(column) != v:t_number || type(finish) != v:t_number ||
          \ row < 1 || row > line('$') || column < 1 || finish <= column ||
          \ get(target.end, 'line', 0) != row || finish > strchars(getline(row)) + 1
      return s:warn('definition range is outside the saved buffer')
    endif
    let byte_column = byteidxcomp(getline(row), column - 1) + 1
    if byte_column < 1
      return s:warn('invalid scalar column in definition response')
    endif
    normal! m'
    call cursor(row, byte_column)
    return 1
  catch
    return s:warn('definition request could not be read or decoded')
  endtry
endfunction
