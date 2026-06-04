; REQUIRES: scip
; COMMAND-LINE: --use-scip-simplex --scip-propagation=probe --scip-propagation-effort=all --arith-prop=none --check-proofs
; COMMAND-LINE: --use-scip-simplex --scip-propagation=basis --scip-propagation-effort=all --arith-prop=none --check-proofs
; EXPECT: unsat
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (>= x 3))
(assert (<= (+ x y) 10))
(assert (>= (- y z) 0))
(assert (or (>= y 100) (>= z 50)))
(check-sat)
