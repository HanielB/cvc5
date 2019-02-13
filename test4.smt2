(set-logic ALL)

(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)

(assert (distinct a b))
; (assert (forall ((x U) (y U)) (= x y)))

(assert (forall ((f (-> U U)) (g (-> U U))) (= f g)))

; (assert (forall ((f (-> U U)) (d U) (r U)) (exists ((g (-> U U))) (forall ((x U)) (= (g x) (ite (= x d) r (f x)))))))

(check-sat)
