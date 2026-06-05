; REQUIRES: scip
; COMMAND-LINE: --use-scip --check-proofs
; EXPECT: unsat
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (> (- x y) 0))
(assert (> (- y z) 0))
(assert (<= (- x z) 0))
(check-sat)
