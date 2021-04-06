;; (x - 2)(x + 2) = x^2 - 4
;; Suppose we know the RHS and want to find an *equivalent formula* LHS:
;; (x - ROOT1)(x + ROOT2) = x^2 - 4
(set-logic NIA)
(declare-const xi Int)
(declare-const r1i Int)
(declare-const r2i Int)
;; Note: don't use xi ** 2 -- gives unsat?
; s.add(ForAll(xi, (xi + r1i) * (xi + r2i) == (xi * xi) - 4  ))
(assert (forall ((xi Int)) (= (* (+ xi r1i) (+ xi r2i)) (- (* xi xi) 4))))
(check-sat)
