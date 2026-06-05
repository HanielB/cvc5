; REQUIRES: scip
; COMMAND-LINE: --use-scip --scip-mip --check-models
; EXPECT: sat
;
; Mixed-integer model with a strict rational bound, found and imported by
; the SCIP exact MIP engine (the delta encoding yields exact values).
(set-logic QF_LIRA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun r () Real)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= (+ (* 2 x) (* 3 y)) 1))
(assert (<= (+ (* 2 x) (* 3 y)) 2))
(assert (> r 0))
(assert (<= (+ r (to_real x)) 2))
(check-sat)
