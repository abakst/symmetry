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

stack build --fast

# Parse --name and --infty and leave the rest
zparseopts -E -D -infty::=INFTY -name::=NAME -worker::=WORKER -job::=JOB

if [[ $# -gt 0 ]]; then
    for f in "$@"; do
        echo "check_file $f $INFTY $NAME $WORKER $JOB"
        check_file $f $INFTY $NAME $WORKER $JOB
    done
    exit 0
fi

ls *.hs | parallel --no-notice -j+0 "./check_file.sh {} $INFTY $NAME $WORKER $JOB"

echo
echo "${BOLD_GREEN}DONE${RESET}"
