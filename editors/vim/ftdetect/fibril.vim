" Fibril file detection only: never build, run, or start external services.
augroup fibril_filetype
  autocmd!
  autocmd BufRead,BufNewFile *.fib if empty(&l:filetype) | setfiletype fibril | endif
augroup END
