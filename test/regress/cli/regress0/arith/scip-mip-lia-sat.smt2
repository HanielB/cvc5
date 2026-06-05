; REQUIRES: scip
; COMMAND-LINE: --use-scip --scip-mip --check-models
; EXPECT: sat
;
; The relaxation has a fractional vertex (x = 1/2), so the integral model
; is found and imported by the SCIP exact MIP engine.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= (+ (* 2 x) (* 3 y)) 1))
(assert (<= (+ (* 2 x) (* 3 y)) 2))
(check-sat)
