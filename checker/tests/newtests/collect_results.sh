#!/bin/zsh

set -e

# traps the 'Ctrl-C' signal, and kills all the children
trap "kill 0" SIGINT

source colors.sh

# worker count -> buffer size
typeset -A WORKER_COUNT_BUFFER_MAP
WORKER_COUNT_BUFFER_MAP=( 
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

typeset -A WJOB_COUNT_BUFFER_MAP
WJOB_COUNT_BUFFER_MAP=( 
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

MAX_JOB_COUNT=10

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
for worker_no in $(echo "${(@k)WORKER_COUNT_BUFFER_MAP}" | tr ' ' '\n' | sort -n); do
    # [[ $worker_no -lt 7 ]] && continue

    echo "\n${BOLD_BLUE}WORKER COUNT: ${worker_no}${RESET}"

    filtered_with_jobs=(${(@)WITH_JOBS})

    for job_no in $(seq 1 ${MAX_JOB_COUNT}); do
        # [[ $job_no -lt 6 ]] && continue

        log_folder=${OUTPUT_ROOT}/${worker_no}_${job_no} 
        mkdir -p $log_folder

        infty=$(( $WJOB_COUNT_BUFFER_MAP[$worker_no] * $job_no ))

        echo "${BOLD_BLUE}JOB COUNT: ${job_no}${RESET}"

        parallel --no-notice --halt never -j+0 \
            --joblog wjob.run \
            "${TEST_ROOT}/run_spin.sh '{1}' '$log_folder' ${infty} --worker=${worker_no} --job=${job_no}" \
            ::: ${filtered_with_jobs} || true


        # awk script will print the indices of the benchmark that succeeds

        new_filter=()

        { awk --posix -f parallel_log_parser.awk wjob.run | while read passed; do
            new_filter+=("${filtered_with_jobs[$passed]}")
        done
        } || { echo "${BOLD_RED}FAIL${RESET}: parsing parallel job log failed"; exit 1 }

        if [[ ${#new_filter} -eq 0 ]]; then
            break
        fi

        filtered_with_jobs=(${(@)new_filter})
    done
done

# !!! REMOVE THIS !!!
exit 0

# only workers, from 1 .. 10
for worker_no in $(echo "${(@k)WORKER_COUNT_BUFFER_MAP}" | tr ' ' '\n' | sort -n); do
    # [[ $worker_no -lt 8 ]] && continue

    log_folder=${OUTPUT_ROOT}/${worker_no}
    mkdir -p $log_folder
    
    infty=$WORKER_COUNT_BUFFER_MAP[$worker_no]
    
    echo "\n${BOLD_BLUE}WORKER COUNT: ${worker_no}${RESET}"
    
    parallel --no-notice --halt 2 -j+0 \
             ${TEST_ROOT}/run_spin.sh \
             "{1}" "$log_folder" ${infty} --worker=${worker_no} \
             ::: ${ONLY_WORKER}
done
