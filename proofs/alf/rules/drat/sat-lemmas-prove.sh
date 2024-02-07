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
smtFile=""
lemmas=""
while read -r line
    do
    if (( count == 0 )) && [[ "$line" == "(" ]]; then
        count=$((count+1))
    elif (( count == 1 )); then
        cnfFile="$line"
        count=$((count+1))
    elif (( count == 2 )); then
        smtFile="$line"
        count=$((count+1))
    elif (( count == 3 )); then
        lemmas="$line"
        count=$((count+1))
    elif (( count == 4 )) && [[ "$line" == ")" ]]; then
        break
    else
        echo "false"
        break
    fi
done < /dev/stdin

# >&2 echo "File with CNF: $cnfFile"
# >&2 echo "File with CNF: $smtFile"
# >&2 echo "Lemmas to prove: $lemmas"

## TODO:
# 1. ensure $cnfFile is unsat
# 2. minimize the lemmas necessary to refute $cnfFile
# 3. check the corresponding lemmas in $lemmas that were in the minimized lemma set

echo "true"
exit 0
