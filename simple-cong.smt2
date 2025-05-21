(set-logic QF_UF)
(set-option :simplification none)

(declare-sort U 0)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a U)
(declare-const b U)
(declare-const c U)
(declare-const d U)
(declare-const e1 U)
(declare-const e2 U)
(declare-fun f (U U) U)

(assert (= a b))
(assert (= c d))
(assert (or (= a e1) (= c e2)))
(assert (or (and (not (= b e1)) (not (= d e2))) p1))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a c) (f b d)))))

(check-sat)
