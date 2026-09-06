; EXPECT: unsat
; Tests the Alethe translation of the elimination of a real division by a
; possibly-zero denominator: the application of the by-zero Skolem function
; is printed as the choice term (choice ((y Real)) (= y (/ x 0.0))), the
; value of the division at zero, and the eliminating equality is the
; conclusion of a div_by_zero_intro step.
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (not (= y 0.0)))
(assert (= (/ x y) 2.0))
(assert (= x (* 3.0 y)))
(check-sat)
