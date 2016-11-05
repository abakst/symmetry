#!/bin/zsh

cat <<'EOF'
\begin{table}\centering
\renewcommand{\arraystretch}{1.2}
\begin{tabular}{@{}llrrr@{}}
\toprule
Benchmark & & Process & Time (s) & Memory (mb) \\
\midrule
EOF

# benchmark,worker,stored,matched,transitions,steps,memory (Mbytes),time (seconds)

to_latex() {
  awk --posix '
BEGIN {
  FS=",";
}

NR > 1 {
  if (max_worker[$1] < $2) {
    max_worker[$1] = $2;
    rows[$1] = sprintf("%-20s & & %-10s & %-10s & %-10s \\\\", $1, $2, $8, $7);
  }
}

END {
  for (k in rows) {
    print rows[k];
  }
}' $1
}

to_latex spin_results.csv

cat <<'EOF'
\bottomrule
\end{tabular}
\caption{Spin results}
\end{table}
EOF

