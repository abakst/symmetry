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
    memory=$1 " " $4;
  }

  if ($0 ~ /.*elapsed time .* seconds/) {
    time=$4 " " $5;
  }
}

END {
  if (ok == 0) {
    exit
  }

  printf("%s,%d,%d,%d,%d,%s,%s\\n", 
    file, stored, matched, transitions, steps, memory, time);
}
EOF
)

# echo $PARSER
# exit 0

for n in $(seq 1 ${NO_OF_TESTS}); do
    for f in ${ONLY_WORKER}; do
        log="results/$n/${f:r}.log"
        awk --posix -f <(echo $PARSER) --assign file=${log:t:r} $log
    done
done
