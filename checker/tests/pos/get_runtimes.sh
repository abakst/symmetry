#!/bin/zsh

parse_time() {
    grep -P '^T:' | awk '{printf("%-24s %s\n",$2, $3)}'
}

for f in *.hs; do
    /usr/bin/time -f "T: $f %U" stack runghc -- $f --rewrite >/dev/null 2>&1 | parse_time
done

