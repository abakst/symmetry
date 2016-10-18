#!/bin/zsh

set -e

# traps the 'Ctrl-C' signal, and kills all the children
trap "kill 0" SIGINT

source colors.sh

# worker count -> buffer size
typeset -A INFTY_MAP
INFTY_MAP=( 
    1  2
    2  2 
    3  3
    4  4
    5  5
    6  6
    7  7
    8  8
    9  9
    10 10
)

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
for worker_no in $(echo "${(@k)INFTY_MAP}" | tr ' ' '\n' | sort -n); do
    [[ $worker_no -lt 9 ]] && continue

    mkdir -p ${OUTPUT_ROOT}/${worker_no}
    
    infty=$INFTY_MAP[$worker_no]
    
    echo "\n${BOLD_BLUE}WORKER COUNT: ${worker_no}${RESET}"
    
    parallel --no-notice --halt 2 -j+0 \
             ${TEST_ROOT}/run_spin.sh "{1}" "${OUTPUT_ROOT}/${worker_no}" ${infty} --worker=${worker_no} \
             ::: ${ONLY_WORKER}
done
