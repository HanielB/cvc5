#!/bin/bash

solver=~/cvc/wt-thf/prod/bin/cvc4
options="--uf-ho --finite-model-find"
traces=""
time=""
ulimit="ulimit -S -t 2"
file="test-unsound.txt"
path="/home/hbarbosa/benchmarks/tptp/Problems/"

echo "Options: $options"
echo "Traces: $traces"
echo

while read name; do
    echo "$solver on $path$name";
    ($ulimit; $time $solver $options $traces  "$path$name")
    echo "=====================================";
done < $file

# for name in ~/benchmarks/tptp/Problems/GRA/*.p; do
# for name in $(find ~/benchmarks/tptp/Problems -name '*.p'); do
#     # Ignoring TH1
#     if grep -q "TH1" "$name"; then
#         continue
#     fi
#     # Ignoring lambdas for now
#     # if grep -q "\^.\[" "$name"; then
#     #     continue
#     # fi
#     # if grep -q "\^\[" "$name"; then
#     #     continue
#     # fi
#     # Only run on problems with thf constructs
#     if grep -q TH0 "$name"; then
#         # echo "$name";
#         echo "$solver on $name";
#         ($ulimit; $time $solver $options $traces "$name")
#         echo "=====================================";
#     fi
# done
