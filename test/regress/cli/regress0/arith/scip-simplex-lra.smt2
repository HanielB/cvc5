; REQUIRES: scip
; COMMAND-LINE: --use-scip-simplex
; EXPECT: sat
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 0))
(assert (< x 1))
(assert (> (+ x y) 2))
(check-sat)
