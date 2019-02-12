(set-logic ALL)

(declare-sort U 0)

(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(declare-fun g (U) U)

(assert (not (= f g)))

(assert (forall ((x U))(= (f x) (g x))))

(check-sat)
