(set-logic QF_UFLIA)
(set-option :simplification none)

(declare-const p1 Bool)
(declare-const p2 Bool)
(declare-const p3 Bool)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e1 Int)
(declare-const e2 Int)
(declare-const e3 Int)
(declare-fun f (Int Int) Int)

(assert (= a b))
(assert (= c d))
; (assert (= e1 e2))
; (assert (= e2 e3))
(assert (and p1 true))
(assert (or (not p1) (and p2 p3)))
(assert (or (not p3) (not (= (f a c) (f b d)))))
;(assert (not (= e1 e3)))

(check-sat)
(exit)

- theory lemma: (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d)))
  - morally an implication (and (= a b) (= c d) (= (f a c) (f b d)))

- interaction with rest of reasoning is by connecting with (= a b) and (= c d) and with the opposite of the conclusion (not (= (f a c) (f b d)))

- input has assumptions (= a b) and (= c d)
- SAT solver has derived (not (= (f a c) (f b d)))

- the connection with the lemma is represented by step

  (step t15 (cl) :rule resolution :premises (t9 t14 a1 a0))
                                             /\  /\ ------ input assumptions
                                        t-lemma  negated conclusion

  
--------------------------------------------------- t9  ------------------------------ t4 ------ a1  ------- a2
(cl (not (= a b)) (not (= c d)) (= (f a c) (f b d)))    (cl (not (= (f a c) (f b d))))    (= a b)    (= c d)
------------------------------------------------------------------------------------------------------------- RES
                                          (cl)


- One thing that would be possible for example is:

                                                        t-lemma'  ...   
--------------------------------------------------- t9  --------------------------------... ------ a1  ------- a2
(cl (not (= a b)) (not (= c d)) (= (f a c) (f b d)))    (cl (not (= (f a c) (f b d))))    (= a b)    (= c d)
------------------------------------------------------------------------------------------------------------- RES
                                          (cl)



