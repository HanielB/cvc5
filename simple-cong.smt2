(set-logic QF_UFLIA)
(set-option :simplification none)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-fun f (Int Int) Int)

(assert (= a b))
(assert (= c d))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a c) (f b d)))))

; (or (not (= a b)) (not (= c d)) (= (f a c) (f b d)))

(check-sat)
