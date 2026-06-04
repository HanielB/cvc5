; REQUIRES: scip
; COMMAND-LINE: --use-scip-simplex
; COMMAND-LINE: --use-scip-simplex --check-proofs
; EXPECT: unsat
;
; SCIP's rational layer coerces constants at or above its infinity
; threshold (1e20) to infinity; encoding the bound below would relax it
; to "true" and answer sat. The SCIP simplex must decline such problems
; and delegate to a conventional procedure. The conflict requires row
; reasoning (x + y <= 2e19 < 2e20), so the check reaches the procedure
; rather than being resolved at assertion time.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (>= (+ x y) 200000000000000000000.0))
(assert (<= x 10000000000000000000.0))
(assert (<= y 10000000000000000000.0))
(check-sat)
