(set-logic ALL)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun h ((-> U U)) U)

(assert (forall ((x U)) (= (f x) a)))
(assert (forall ((x U)) (= (g x) a)))

(assert (= (h f) b))
(assert (not (= (h g) b)))

(check-sat)
