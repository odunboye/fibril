" Lexical highlighting for the current Fibril subsets; not semantic checking.
if exists('b:current_syntax')
  finish
endif
let s:save_cpo = &cpo
set cpo&vim

" Apostrophes belong to ASCII identifiers; if' is not the keyword if.
syntax iskeyword @,48-57,_,39

syntax keyword fibrilKeyword let in case of return if then else module import export record constructor eliminator where projection
syntax keyword fibrilType Type Unit Bool String
syntax keyword fibrilBoolean True False
" IO/putStrLn are resolved names; do and module headers are syntax, not typing evidence.
syntax keyword fibrilConsoleKeyword do
syntax keyword fibrilConsoleType IO
syntax keyword fibrilConsoleFunction putStrLn

syntax match fibrilNumber /\<[0-9]\+\>/
syntax match fibrilQuantity /\<[01]\ze\s\+[A-Za-z_][A-Za-z0-9_']*\s*:/
syntax match fibrilDeclaration /^\%([01]\s\+\)\?[A-Za-z_][A-Za-z0-9_']*\ze\s*\%(:\|=\%([>]\)\@!\)/ contains=fibrilQuantity
syntax match fibrilOperator /<-\|->\|=>\|[\\=:λ→⇒.]/
syntax match fibrilDelimiter /[()]/

" Later valid-escape rules take precedence over the contained error match.
syntax match fibrilBadEscape /\\./ contained
syntax match fibrilBadEscape /\\$/ contained
syntax match fibrilEscape /\\["\\nrt]/ contained
syntax match fibrilRawControl /\t/ contained
syntax region fibrilString start=/"/ skip=/\\\\\|\\"/ end=/"\|$/ oneline
      \ contains=fibrilEscape,fibrilBadEscape,fibrilRawControl

syntax keyword fibrilTodo TODO FIXME XXX NOTE contained
syntax match fibrilComment /--.*$/ contains=fibrilTodo,@Spell

highlight default link fibrilKeyword Keyword
highlight default link fibrilType Type
highlight default link fibrilBoolean Boolean
highlight default link fibrilConsoleKeyword Keyword
highlight default link fibrilConsoleType Type
highlight default link fibrilConsoleFunction Function
highlight default link fibrilNumber Number
highlight default link fibrilQuantity Special
highlight default link fibrilDeclaration Identifier
highlight default link fibrilOperator Operator
highlight default link fibrilDelimiter Delimiter
highlight default link fibrilString String
highlight default link fibrilEscape SpecialChar
highlight default link fibrilBadEscape Error
highlight default link fibrilRawControl Error
highlight default link fibrilComment Comment
highlight default link fibrilTodo Todo

let b:current_syntax = 'fibril'
let &cpo = s:save_cpo
unlet s:save_cpo
