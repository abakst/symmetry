#!/bin/zsh

# benchmark,worker,stored,matched,transitions,steps,memory (Mbytes),time (seconds)

cat <<'EOF'
\begin{table}\centering
\renewcommand{\arraystretch}{1.2}
\begin{tabular}{@{}llrrr@{}}
\toprule
Benchmark & & Process & Time (s) & Memory (mb) \\
\midrule
EOF

worker_to_latex() {
  awk --posix '
BEGIN {
  FS=",";
}

NR > 1 {
  if (max_worker[$1] < $2) {
    max_worker[$1] = $2;
    rows[$1] = sprintf("%s & & %s & %s & %s \\\\", $1, $2, $8, $7);
  }
}

END {
  for (k in rows) {
    print rows[k];
  }
}' $1
}

# benchmark,worker,job,stored,matched,transitions,steps,memory (Mbytes),time (seconds)

worker_w6jobs_to_latex() {
  awk --posix '
BEGIN {
  FS = ",";
}

NR > 1  {
  if ($3 == 6) {
    if (max_worker[$1] < $2) {
      max_worker[$1] = $2;
      rows[$1] = sprintf("%s & & %s & %s & %s \\\\", $1, $2, $9, $8);
    }
  }
}

END {
  for (k in rows) {
    print rows[k];
  }
}' $1
}

worker_to_latex        only_worker.csv
worker_w6jobs_to_latex worker_with_jobs.csv

cat <<'EOF'
\bottomrule
\end{tabular}
\caption{Spin results}
\end{table}
EOF

