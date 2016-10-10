#!/bin/zsh
# vim: set foldmethod=marker:

# colors {{{
autoload colors
if [[ "$terminfo[colors]" -gt 8 ]]; then
    colors
fi
for COLOR in RED GREEN YELLOW BLUE MAGENTA CYAN BLACK WHITE; do
    eval $COLOR='$fg_no_bold[${(L)COLOR}]'
    eval BOLD_$COLOR='$fg_bold[${(L)COLOR}]'
done
eval RESET='$reset_color'
# }}}

for hs in *.hs; do
  stack runghc -- $hs --verify &>/dev/null \
    && { echo "${BOLD_GREEN}PASS${RESET}: $hs" } \
    || { echo "${BOLD_RED}FAIL${RESET}: $hs" }
done
