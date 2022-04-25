#!/bin/bash

./prod/bin/cvc5 --produce-proofs --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 $@ > tmp.alethe
tail -n +2 tmp.alethe > pf.alethe
alethe-proof-checker check pf.alethe $1

# error: /alethe-check.sh /home/hbarbosa/benchmarks/isabelle-mirabelle/Green_cvc42/x2020_07_31_07_47_44_761_6850464.smt_in --produce-proofs --proof-format-mode=alethe --proof-granularity=theory-rewrite --lang=smt2 --dag-thresh=0
