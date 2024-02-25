; EXPECT: unsat
;; Carcara does not yet support the unicode representation of characters.
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x Int)
(declare-fun v () String)
(assert (and (> 0 x) (distinct 0 (ite (= "\n" (str.at v 0)) 1 0))))
        (and (> 0 x) (distinct 0 (ite (= "\u{5c}n" (str.at v 0)) 1 0)))
(check-sat)
