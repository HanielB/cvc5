(set-logic ALL)

(declare-fun f (Int Int) Int)
(declare-fun g (Int) (-> Int Int))
(declare-fun h () (-> Int Int Int))

(declare-fun k ((-> (-> Int Int) (-> Int Int) Int)) Int)

; (assert (and (= f g) (= g h)))

; (assert (= (f 1 2) 5))
; (assert (= (f 2 1) 7))

; (check-sat)
