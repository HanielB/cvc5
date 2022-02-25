(set-logic QF_UF)

(declare-sort U 0)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)

(assert (= a b))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a) (f b)))))

(check-sat)
