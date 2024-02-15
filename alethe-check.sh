#!/bin/bash

# tfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1
tfile="/home/hbarbosa/cvc5/wt-proofnew/pf.alethe"

./prod/bin/cvc5 --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 --dump-proofs  $@ | tail -n +2 > $tfile
~/carcara/target/release/carcara check --allow-int-real-subtyping --expand-let-bindings $tfile $1
