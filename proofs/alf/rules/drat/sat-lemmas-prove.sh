#!/usr/bin/env bash

# This reads exactly one function call from stdin, and returns
# true if it is as expected:
# (
# "name of CNF file"
# "name of original SMT-LIB problem"
# t
# )

count=0
cnfFile=""
lemmas=""
while read -r line
    do
    if (( count == 0 )) && [[ "$line" == "(" ]]; then
        count=$((count+1))
    elif (( count == 1 )); then
        cnfFile="$line"
        count=$((count+1))
    elif (( count == 2 )); then
        lemmas="$line"
        count=$((count+1))
    elif (( count == 3 )) && [[ "$line" == ")" ]]; then
        break
    else
        echo "false"
        break
    fi
done < /dev/stdin

# >&2 echo "File with CNF: $cnfFile"
# >&2 echo "Lemmas to prove: $lemmas"

echo "true"
exit 0
