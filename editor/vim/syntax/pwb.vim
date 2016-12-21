if exists("b:current_syntax")
    finish
endif
let b:current_syntax="pwb"

syn keyword PWBTodo contained TODO FIXME XXX NOTE
" syn match PWBComment "#.*$" contains=PWBTodo
"syn match PWBVar "`\s*\w\+"
" syn match Type ":\s*\w\+"
" syn region PWBType start=":"hs=e+1 end="fn\|name\|var\|rw"he=s-1 contains=PWBKeywords

syn match PWBComment "--.*$"
syn region PWBComment start="(\*" end="\*)" contains=PWBTodo
syn region PWBParam start=+"+ end=+"+

syn match PWBOp "<="
syn match PWBOp "\[\]"
syn match PWBOp "<"
syn match PWBOp ">"

syn keyword PWBKeywords case new
" syn keyword PWBOp =>

hi def link PWBParam Include
hi def link PWBKeywords Keyword
hi def link PWBOp   Operator
hi def link PWBComment Comment
hi def link PWBTodo Todo
hi def link PWBVar Special
hi def link PWBType Type
