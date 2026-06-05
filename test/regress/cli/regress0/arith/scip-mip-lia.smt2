; REQUIRES: scip
; COMMAND-LINE: --use-scip --scip-mip
; COMMAND-LINE: --scip-mip
; COMMAND-LINE: --use-scip --scip-mip --check-proofs
; EXPECT: unsat
;
; Satisfiable over the rationals (x = 1/2) but not over the integers: the
; SCIP exact MIP engine establishes the infeasibility. Without proofs its
; verdict is trusted (a conflict over the asserted bounds); with proofs
; SCIP's certificate is reconstructed into a cvc5 proof of the conflict.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= (+ (* 2 x) (* 3 y)) 1))
(assert (<= (+ (* 2 x) (* 3 y)) 1))
(check-sat)
