; COMMAND-LINE: --cegqi-full
; EXPECT: unsat
;; introduces quantifiers Skolem in an illegal way
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-info :status unsat)
(assert
 (not
  (exists
   ((a (_ BitVec 32))
    (b (_ BitVec 32))
    (c (_ BitVec 32))
    (d (_ BitVec 32))
    (e (_ BitVec 32)))
   (distinct (bvashr c b) (bvlshr d a) e))))
(check-sat)
