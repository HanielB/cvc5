#!/bin/bash

# tfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1
tfile="/home/hbarbosa/cvc5/wt-alethe/test.alethe"

./prod/bin/cvc5 --proof-format=alethe --lang=smt2 --dump-proofs --dag-thresh=0  $@ | tail -n +2 > $tfile
~/carcara/target/release/carcara check --no-print-with-sharing --allow-int-real-subtyping --expand-let-bindings -i $tfile $1
