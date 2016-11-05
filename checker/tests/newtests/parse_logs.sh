#!/bin/zsh

set -e

source colors.sh

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

#  if (job == 0) {
    printf("%s,%d,%d,%d,%d,%d,%s,%s\\n",
      benchmark, worker, stored, matched, transitions, steps, memory, time);
#  } else {
#    printf("%s,%d,%d,%d,%d,%d,%d,%s,%s\\n",
#      benchmark, worker, job, stored, matched, transitions, steps, memory, time);
#  }
}
EOF
)

print_title() {
    echo "benchmark,worker,stored,matched,transitions,steps,memory (Mbytes),time (seconds)";
}

list_wjob_tests() {
    for d in results/*_*/*.log; do echo $d; done | \
        sed -n 's|results/\([0-9]\+\)_\([0-9]\+\)/\(.*\)\.log|\3 \1 \2|p' | \
        sort -k 1 -k 2 -n -k 3 -n

}

with_jobs_csv() {
    list_wjob_tests | while read benchmark worker_count job_count; do
        [[ ${job_count} -eq 6 ]] || continue
        # printf "%-20s %-5d %-5d\n" "$benchmark" "$worker_count" "$job_count"
        awk --posix -f <(echo $PARSER) \
            --assign benchmark=${benchmark} \
            --assign worker=${worker_count} \
            --assign job=${job_count} \
            "results/${worker_count}_${job_count}/$benchmark.log"
    done
}

list_only_worker_tests() {
    for d in results/*/*.log; do echo $d; done | \
        sed -n 's|results/\([0-9]\+\)/\(.*\)\.log|\2 \1|p' | \
        sort -k 1 -k 2 -n

}

only_worker_csv() {
    list_only_worker_tests | while read benchmark worker_count; do
        # printf "%-20s %-5d\n" "$benchmark" "$worker_count"
        awk --posix -f <(echo $PARSER) \
            --assign benchmark=${benchmark} \
            --assign worker=${worker_count} \
            "results/${worker_count}/$benchmark.log"
    done

}

# redirect the output to spin_results.csv
print_title      > spin_results.csv
only_worker_csv >> spin_results.csv
with_jobs_csv   >> spin_results.csv

