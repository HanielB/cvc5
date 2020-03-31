./debug/bin/cvc4 --dump-proof --no-expand-definitions-pp --no-unconstrained-simp --produce-unsat-cores --no-apply-subst --no-static-learning --simplification=none --no-repeat-simp --no-global-negate --no-symmetry-breaker --no-pb-rewrites --no-theory-preprocess --no-sort-inference --no-pre-skolem-quant --no-bv-eq --no-bv-ineq --no-bv-algebraic --no-bv-to-bool --bool-to-bv=off --no-bv-intro-pow2 --no-bitblast-aig  "$@"

# to get rid of "unsat being in the proof file"
# | tail -n+2 > qf-unsat-01-nary_cvc4.lean



##### USAGE
#### add after ./run-debug-cvc.sh

# qf-unsat-01-nary.smt2 --new-proof -d theory::explain
