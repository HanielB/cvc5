(set-logic ALL)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U U U) U)
(declare-fun g (U U U) U)

(assert (not (= (f a) (g b))))

(assert (forall ((x U))(= (f a x) (g b x))))

(check-sat)
