" To make use this file an entry `set exrc` is needed in your vimrc file

autocmd FileType xml setlocal 
    \ formatexpr=format#Format() 
    \ indentexpr=
    \ softtabstop=2
    \ tabstop=2
    \ shiftwidth=2
    \ textwidth=80
    \ noexpandtab
