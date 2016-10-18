#!/bin/zsh
# vim: set foldmethod=marker:

set -e

# traps the 'Ctrl-C' signal, and kills all the children
trap "kill 0" SIGINT

OUTPUT_ROOT="${0:A:h}/results"

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

run_spin() {
  if [[ $# -le 3 ]]; then 
      echo "${BOLD_RED}ERROR${RESET}: not enough arguments to run_spin"
      exit 1
  fi

  local FILE="$1"
  local NAME=${FILE:r}          # without the extension
  local OUTPUT="$2"
  local INFTY=$3
  shift 3

  stack runghc -- $FILE --dump-model --name "$NAME" $@ &>/dev/null || \
      { echo "${BOLD_RED}FAIL${RESET}: $FILE [runghc]"; exit 1 }
  
  pushd .symcheck.${NAME}

  spin -m -a -D__K__=${INFTY} out.pml &>/dev/null || \
      { echo "${BOLD_RED}FAIL${RESET}: $FILE [spin]"; exit 1 }

  cc -O2 -DVECTORSZ=2048 -DSAFETY -DNOBOUNDCHECK -DNOCOMP -DSFH -DNOFAIR -o pan pan.c &>/dev/null || \
      { echo "${BOLD_RED}FAIL${RESET}: $FILE [cc]"; exit 1 }
  
  local OUT_LOG=${OUTPUT}/${NAME}.log

  ./pan -X -n -m1000000 > ${OUT_LOG} || \
      { echo "${BOLD_RED}FAIL${RESET}: $FILE [pan]"; exit 1 }
  
  grep -qPi 'pan:[0-9]+:\s+invalid end state' ${OUT_LOG} && \
      { echo "${BOLD_RED}FAIL${RESET}: $FILE [pan - invalid end state]"; exit 1 }

  printf "${BOLD_GREEN}DONE${RESET}: %-20s $@\n" ${FILE} 
  popd
}

run_spin $@

