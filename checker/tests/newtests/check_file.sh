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

check_file() {
  local FILE="$1"
  local NAME=${FILE:r}          # without the extension
  shift
  stack runghc -- $FILE --verify --name "$NAME" $@ &>/dev/null \
    && { echo "${BOLD_GREEN}PASS${RESET}: $FILE" } \
    || { echo "${BOLD_RED}FAIL${RESET}: $FILE" }
}

check_file $@

