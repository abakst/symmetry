#!/bin/zsh

l_orig=(ali veli deli)
out="1\n"

l=(${(@)l_orig})

new=""
printf "$out" | while read n; do
    echo "1:|$n|"
    new="$new ${l[$n]}"  
done

echo $new | sed 's/^\s+//' | read new

if [[ -z "$new" ]]; then
    exit 0
fi

echo "2:|$new|"
l=("${(@s/ /)new}")
echo ${#l}

