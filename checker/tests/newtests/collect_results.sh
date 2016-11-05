#!/bin/zsh

set -e

# traps the 'Ctrl-C' signal, and kills all the children
trap "kill 0" SIGINT

source colors.sh

# worker count -> buffer size
typeset -A WORKER_COUNT_BUFFER_MAP
WORKER_COUNT_BUFFER_MAP=( 
    1  2
    # 2  2 
    # 3  3
    # 4  4
    # 5  5
    # 6  6
    # 7  7
    # 8  8
    # 9  9
    10 10
    # 11  11
    # 12  12
    # 13  13
    # 14  14
    # 15  15
    # 16  16
    # 17  17
    # 18  18
    # 19  19
    20  20
    21 21
    30 30
    40 40
    50 50
    60 60
    70 70
    80 80
    90 90
    100 100
    1000 1000
    10000 10000
)

typeset -A WJOB_COUNT_BUFFER_MAP
WJOB_COUNT_BUFFER_MAP=( 
    # 1  2
    # 2  2 
    # 3  3
    # 4  4
    # 5  5
    # 6  6
    # 7  7
    # 8  8
    # 9  9
    # 10 10
    # 11  11
    # 12  12
    # 13  13
    # 14  14
    # 15  15
    # 16  16
    # 17  17
    # 18  18
    # 19  19
    # 20  20
    # 30 30
    # 40 40
    # 50 50
    # 60 60
    # 70 70
    # 80 80
    # 90 90
    # 100 100
    1000 1000
    10000 10000
)

MAX_JOB_COUNT=10

ONLY_WORKER=( # ConcDB.hs
              # DatabaseSample.hs
              # PingMulti00.hs
              PingMulti02.hs
              # PingMulti03.hs
              # PingMulti2Party.hs
              # PingMultiSize.hs
              # PingRace00.hs
              # Registry.hs
              # WorkPushing.hs
            )

WITH_JOBS=( # WorkStealing.hs
            WorkStealingxx.hs
            # MapReduce.hs
          )

TEST_ROOT=${0:A:h}
OUTPUT_ROOT="${TEST_ROOT}/results"

tester_for_work_and_jobs() {
    local -a filtered_with_jobs    
    local job_no=6
    filtered_with_jobs=(${(@)WITH_JOBS})

    # only workers, from 1 .. 10
    for worker_no in $(echo "${(@k)WJOB_COUNT_BUFFER_MAP}" | tr ' ' '\n' | sort -n); do
        # [[ $worker_no -lt 7 ]] && continue

        echo "\n${BOLD_BLUE}WORKER COUNT: ${worker_no}${RESET}"

        # for job_no in $(seq 1 ${MAX_JOB_COUNT}); do
        #     [[ $job_no -ne 6 ]] && continue

        local log_folder=${OUTPUT_ROOT}/${worker_no}_${job_no} 
        mkdir -p $log_folder

        local infty=$(( $WJOB_COUNT_BUFFER_MAP[$worker_no] * $job_no ))

        echo "${BOLD_BLUE}JOB COUNT: ${job_no}${RESET}"

        parallel --no-notice --halt never -j+0 \
            --joblog wjob.run \
            "${TEST_ROOT}/run_spin.sh '{1}' '$log_folder' ${infty} --worker=${worker_no} --job=${job_no}" \
            ::: ${filtered_with_jobs} || true


        # awk script will print the indices of the benchmark that succeeds

        local -a new_filter
        new_filter=()

        { awk --posix -f parallel_log_parser.awk wjob.run | while read passed; do
            new_filter+=("${filtered_with_jobs[$passed]}")
        done } || { echo "${BOLD_RED}FAIL${RESET}: parsing parallel job log failed"; exit 1 }

        if [[ ${#new_filter} -eq 0 ]]; then
            break
        fi

        local -a filtered_with_jobs    
        filtered_with_jobs=(${(@)new_filter})
        # done
    done
}

tester_for_work_only() {

    local -a filtered_only_worker
    filtered_only_worker=(${(@)ONLY_WORKER})

    # only workers, from 1 .. 10
    for worker_no in $(echo "${(@k)WORKER_COUNT_BUFFER_MAP}" | tr ' ' '\n' | sort -n); do
        # [[ $worker_no -lt 8 ]] && continue

        local log_folder=${OUTPUT_ROOT}/${worker_no}
        mkdir -p $log_folder

        local infty=$WORKER_COUNT_BUFFER_MAP[$worker_no]

        echo "\n${BOLD_BLUE}WORKER COUNT: ${worker_no}${RESET}"

        parallel --no-notice --halt never -j+0 \
            --joblog wjob.run \
            "${TEST_ROOT}/run_spin.sh '{1}' '$log_folder' ${infty} --worker=${worker_no}" \
            ::: ${filtered_only_worker} || true

        local -a new_filter
        new_filter=()

        { awk --posix -f parallel_log_parser.awk wjob.run | while read passed; do
            new_filter+=("${filtered_only_worker[$passed]}")
        done } || { echo "${BOLD_RED}FAIL${RESET}: parsing parallel job log failed"; exit 1 }

        if [[ ${#new_filter} -eq 0 ]]; then
            break
        fi

        local -a filtered_only_worker
        filtered_only_worker=(${(@)new_filter})
    done
}

tester_for_work_only

# tester_for_work_and_jobs
