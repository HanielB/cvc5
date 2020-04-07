./debug/bin/cvc4 --dump-proof --no-expand-definitions-pp --no-unconstrained-simp --produce-unsat-cores --no-apply-subst --no-static-learning --simplification=none --no-repeat-simp --no-global-negate --no-symmetry-breaker --no-pb-rewrites --no-theory-preprocess --no-sort-inference --no-pre-skolem-quant --no-bv-eq --no-bv-ineq --no-bv-algebraic --no-bv-to-bool --bool-to-bv=off --no-bv-intro-pow2 --no-bitblast-aig  "$@"

# to get rid of "unsat being in the proof file"
# | tail -n+2 > qf-unsat-01-nary_cvc4.lean



##### USAGE
#### add after ./run-debug-cvc.sh

# qf-unsat-01-nary.smt2 --new-proof -d theory::explain


########## Good for debugging equality engine proofs

# set args --dump-proof --no-expand-definitions-pp --no-unconstrained-simp --produce-unsat-cores --no-apply-subst --no-static-learning --simplification=none --no-repeat-simp --no-global-negate --no-symmetry-breaker --no-pb-rewrites --no-theory-preprocess --no-sort-inference --no-pre-skolem-quant --no-bv-eq --no-bv-ineq --no-bv-algebraic --no-bv-to-bool --bool-to-bv=off --no-bv-intro-pow2 --no-bitblast-aig  ~/cvc/wt-tbpf/qf-unsat-06-cc-negtrans.smt2 --new-proofs --proof-format=lean -d theory::explain --default-dag-thresh=0 -d newproof::sat -d newproof::pm::th -d pf::ee -d eq-exp -d equality
