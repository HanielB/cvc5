(set-logic ALL)
(set-info :status sat)
(declare-datatypes ((P 0)) (((k (f Real)))))
(declare-const r P)
(assert (= 0.0 (f r)))
(check-sat)
