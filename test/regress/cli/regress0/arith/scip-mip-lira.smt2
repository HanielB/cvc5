; REQUIRES: scip
; COMMAND-LINE: --use-scip
; COMMAND-LINE: --use-scip --check-proofs
; EXPECT: unsat
;
; Unsatisfiable only through the interplay of integrality and the strict
; bound (with r >= 0 instead, x = 1, y = 0, r = 0 is a model): exercises
; the delta encoding of strict bounds within the exact MIP and, with
; proofs, the reconstruction of its certificate into a cvc5 proof.
(set-logic QF_LIRA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun r () Real)
(assert (>= x 0))
(assert (>= y 0))
(assert (>= (+ (* 2 x) (* 3 y)) 1))
(assert (<= (+ (* 2 x) (* 3 y)) 2))
(assert (> r 0))
(assert (<= (+ r (to_real x)) 1))
(check-sat)
