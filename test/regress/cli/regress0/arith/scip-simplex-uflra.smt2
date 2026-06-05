; REQUIRES: scip
; COMMAND-LINE: --use-scip --check-proofs
; EXPECT: unsat
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (<= x y))
(assert (>= x y))
(assert (not (= (f x) (f y))))
(check-sat)
