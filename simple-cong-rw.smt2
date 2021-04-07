(set-logic QF_UFLIA)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a Int)
(declare-const b Int)
(declare-fun f (Int) Int)

(assert (= a b))
(assert (or (not p3) (not (= (f (+ a 0)) (f b)))))
(assert p1)
(assert (or (not p1) (and p2 p3)))

(check-sat)
