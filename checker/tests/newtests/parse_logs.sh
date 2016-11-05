#!/bin/zsh

set -e

source colors.sh

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

NO_OF_TESTS=10

PARSER=$(cat <<'EOF'
BEGIN {
  ok = 0;
}

NF > 0 {
  if ($0 ~ /[0-9]+ states, stored/) {
    ok = 1;
    stored=$1;
  }

  if ($0 ~ /[0-9]+ states, matched/) {
    matched=$1;
  }

  if ($0 ~ /^\\s+[0-9]+ transitions/) {
    transitions=$1;
  }

  if ($0 ~ /[0-9]+ atomic steps/) {
    steps=$1;
  }

  if ($0 ~ /memory usage/) {
    # memory=$1 " " $4;
    # looks like it's always Mbytes
    memory=$1;
  }

  if ($0 ~ /.*elapsed time .* seconds/) {
    # time=$4 " " $5;
    # looks like it's always seconds
    time=$4;
  }
}

END {
  if (ok == 0) {
    exit
  }

  if (job == 0) {
    printf("%s,%d,%d,%d,%d,%d,%s,%s\\n",
      benchmark, worker, stored, matched, transitions, steps, memory, time);
  } else {
    printf("%s,%d,%d,%d,%d,%d,%d,%s,%s\\n",
      benchmark, worker, job, stored, matched, transitions, steps, memory, time);
  }
}
EOF
)

with_jobs_csv() {
  echo "benchmark,worker,job,stored,matched,transitions,steps,memory (Mbytes),time (seconds)";
  local max_worker=10;
  local max_job=10;

  for worker_count in $(seq 1 ${max_worker}); do
    for job_count in $(seq 1 ${max_job}); do

      local folder="results/${worker_count}_${job_count}"

      [[ -d $folder ]] || continue

      for log in ${folder}/*.log; do
        awk --posix -f <(echo $PARSER) \
          --assign benchmark=${log:t:r} \
          --assign worker=${worker_count} \
          --assign job=${job_count} \
          $log
      done
    done
  done
}

with_jobs_csv > worker_with_jobs.csv

only_worker_csv() {
    echo "benchmark,worker,stored,matched,transitions,steps,memory (Mbytes),time (seconds)";
    for n in $(seq 1 ${NO_OF_TESTS}); do
        for f in ${ONLY_WORKER}; do
            log="results/$n/${f:r}.log"
            awk --posix -f <(echo $PARSER) \
                --assign benchmark=${log:t:r} \
                --assign worker=$n \
                $log
        done
    done
}

only_worker_csv > only_worker.csv

