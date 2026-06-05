; REQUIRES: scip
; COMMAND-LINE: --use-scip
; EXPECT: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> (+ (* 2 x) (* 3 y)) 7))
(assert (< x 4))
(assert (>= y 0))
(assert (<= y 3))
(check-sat)
