#!/bin/zsh
# vim: set foldmethod=marker:

# traps the 'Ctrl-C' signal, and kills all the children
trap "kill 0" SIGINT

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

K=2

get_state_count() {
  local FILE="$1"
  local NAME=${FILE:r}          # without the extension
  shift
  stack runghc -- $FILE --dump-model &>/dev/null \
    || { echo "${BOLD_RED}FAIL${RESET}: $FILE"; exit 1 }

  pushd .symcheck

  spin -m -a -D__K__=${K} out.pml &>/dev/null

  cc -O2 -DVECTORSZ=2048 -DSAFETY -DNOBOUNDCHECK -DNOCOMP -DSFH -DNOFAIR -o pan pan.c &>/dev/null

  STATE_COUNT=$(./pan -X -n -m1000000 | sed -n 's/^\s*\([0-9]*\) states, stored/\1/p')
  printf '%s %d\n' $NAME $STATE_COUNT

  # ./pan -X -n -m1000000 > ../${NAME}-${K}.result

  popd
}

stack build --fast

# Parse --name and --infty and leave the rest
zparseopts -D -E -- i:=INFTY

if [[ ${#INFTY[@]} -gt 0 ]]; then
  K=$INFTY[2]
fi

if [[ $# -gt 0 ]]; then
    for f in "$@"; do
        get_state_count $f
    done
    exit 0
fi

# for hs in *.hs; do
for hs in *.hs; do
    { echo $IGNORED | grep $hs &>/dev/null } && continue
    get_state_count $hs
done

echo
echo "${BOLD_GREEN}DONE${RESET}"
