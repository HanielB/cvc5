#!/bin/bash

#### To use this it's necessary to:
# cd ~/lean-smt
# elan self update
# LEAN_PATH=./build/lib:./lake-packages/std/build/lib:./lake-packages/mathlib/build/lib:./lake-packages/Qq/build/lib:./lake-packages/aesop/build/lib:/home/hbarbosa/.elan/toolchains/leanprover--lean4---nightly-2023-01-16/lib/lean; export LEAN_PATH
# lean $tfile

### Alternatively, without setting the LEAN_PATH, could do (after copying the proof to ~/lean-smt/Smt/):
# lake build +Smt.$fileName &> /tmp/$fileName

tfile="$(mktemp /tmp/fooXXXXXXXXX.lean)" || exit 1
fileName="$(echo $tfile | rev | cut -d'/' -f1 | rev | cut -d'.' -f1)"
echo "/tmp/$fileName.lean"
# tfile="/home/hbarbosa/cvc/wt-leanPrinter/pf.lean" || exit 1

# produce proof, remove first line (which is "unsat"), then remove
# last line (which is closing the s-expression string), then remove
# the s-expression/string prefix

./prod/bin/cvc5 -q --dump-proofs --proof-format=lean --proof-granularity=theory-rewrite --dag-thresh=0 $@ | tail -n +2 | head -n -1 | sed 's/(proof \"//' > $tfile
if ! grep -q -v "unsat" $tfile; then
    echo "ERROR-CVC5"
    exit
fi

# cd ~/lean-smt
# lean $tfile &> /tmp/$fileName
~/lean/process_lean_smt $tfile &> /tmp/$fileName
cd - > /dev/null
if ! grep -q "error" /tmp/$fileName; then
  echo "SUCCESS"
else
  echo "ERROR-LEAN"
fi
