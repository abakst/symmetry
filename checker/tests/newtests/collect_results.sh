#!/bin/zsh

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

typeset -A INFTY_MAP
# worker count -> buffer size
INFTY_MAP=( 
    1 2
    2 2 
    3 3
    4 4
)
CUR_NO=4

ONLY_WORKER=( ConcDB.hs
              DatabaseSample.hs
              PingMulti00.hs
              PingMulti02.hs
              PingMulti03.hs
              PingMulti2Party.hs
              PingMultiSize.hs
              PingRace00.hs
              Registry.hs
              WorkPushing.hs
            )

WITH_JOBS=( WorkStealing.hs
            WorkStealingxx.hs
            MapReduce.hs
          )

TEST_ROOT=${0:A:h}
OUTPUT_ROOT="${TEST_ROOT}/results"

# only workers, from 1 .. 10

#for worker_no in $(seq 1 10); do
for worker_no in $(seq ${CUR_NO} ${CUR_NO}); do
    mkdir -p ${OUTPUT_ROOT}/${worker_no}
    
    infty=$INFTY_MAP[$worker_no]
    
    echo "\n${BOLD_BLUE}WORKER COUNT: ${worker_no}${RESET}"
    
    parallel --no-notice --halt 2 -j+0 \
             ${TEST_ROOT}/run_spin.sh "{1}" "${OUTPUT_ROOT}/${worker_no}" ${infty} --worker=${worker_no} \
             ::: ${ONLY_WORKER}
done
