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

# IGNORED=$(cat <<EOF
# PingMulti2Party.hs
# PingLoopBounded.hs
# EOF
# )

check_file() {
    local FILE="$1"
    local NAME=${FILE:r}          # without the extension
    stack runghc -- $FILE --verify &>/dev/null --name "$NAME" \
        && { echo "${BOLD_GREEN}PASS${RESET}: $FILE" } \
        || { echo "${BOLD_RED}FAIL${RESET}: $FILE" }
}

stack build --fast

if [[ $# -eq 1 ]]; then
    check_file $@
    exit 0
fi

# for hs in *.hs; do
for hs in *.hs; do
    { echo $IGNORED | grep $hs &>/dev/null } && continue
    check_file $hs &            # run the benchmark in background
done

# wait for benchmarks to finish
wait

echo
echo "${BOLD_GREEN}DONE${RESET}"
