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

IGNORED=$(cat <<EOF
PingMulti2Party.hs
PingLoopBounded.hs
EOF
)

check_file() {
  local FILE="$1"
  stack runghc -- $FILE --verify &>/dev/null \
    && ( echo "${BOLD_GREEN}PASS${RESET}: $FILE" ) \
    || ( echo "${BOLD_RED}FAIL${RESET}: $FILE" )
}

if [[ $# -eq 1 ]]; then
  check_file $@
  exit 0
fi

# for hs in *.hs; do
for hs in *.hs; do
  ( echo $IGNORED | grep $hs &>/dev/null ) && continue
  check_file $hs
done
