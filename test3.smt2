(set-logic ALL)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U U U) U)
(declare-fun g (U U) U)

(assert (not (= (f a) g)))

(assert (forall ((x U))(= (f a x) (g x))))

(check-sat)
