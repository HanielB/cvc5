(set-logic ALL)
(set-info :status unsat)

(declare-fun s () String)
(declare-fun t () String)
(declare-fun r () String)
; solvable if we do equality reasoning over str.indexof
(assert (= t s))
(assert (not (= (str.indexof t r 0) (str.indexof s r 0))))
(check-sat)