(set-logic ALL)
(declare-sort $$unsorted 0)

(declare-fun mvalid ((-> $$unsorted Bool)) Bool)
(assert (= mvalid (lambda ((Phi (-> $$unsorted Bool))) (forall ((W $$unsorted)) (Phi W) ))))

(declare-fun mforall_prop ((-> (-> $$unsorted Bool) $$unsorted Bool) $$unsorted) Bool)
(assert (= mforall_prop (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted)) (forall ((P (-> $$unsorted Bool))) (Phi P W) ))))

(declare-fun mnot ((-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mnot (lambda ((Phi (-> $$unsorted Bool)) (W $$unsorted)) (not (Phi W)))))

(declare-fun mor ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mor (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (W $$unsorted)) (or (Phi W) (Psi W)))))

(declare-fun mimplies ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mimplies (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (W $$unsorted)) (mor (mnot Phi) Psi W))))

(declare-fun mbox ((-> $$unsorted $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mbox (lambda ((R (-> $$unsorted $$unsorted Bool)) (Phi (-> $$unsorted Bool)) (W $$unsorted)) (forall ((V $$unsorted)) (or (not (R W V)) (Phi V)) ))))

;;; here: unknown

; (assert (not (forall ((R (-> $$unsorted $$unsorted Bool)))
;                (mvalid
;                  (mforall_prop
;                    (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))

;                      (forall ((P (-> $$unsorted Bool))) (or (not (forall ((V $$unsorted)) (or (not (R W V)) (or (A V) (P V))) ))
;                              (or
;                                (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
;                                (forall ((V $$unsorted)) (or (not (R W V)) (P V)) ))
;                              ))

;                      ))) )))

;;;; up to here: unsat

; (assert (not (forall ((R (-> $$unsorted $$unsorted Bool)))
;                (mvalid
;                  (mforall_prop
;                    (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
;                      (mforall_prop
;                        (lambda ((B (-> $$unsorted Bool)) (W $$unsorted))
;                          (or (not (forall ((V $$unsorted)) (or (not (R W V)) (or (A V) (B V))) ))
;                              (or
;                                (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
;                                (forall ((V $$unsorted)) (or (not (R W V)) (B V)) ))
;                              )
;                          )
;                        W)))) )))

; (assert (not (forall ((R (-> $$unsorted $$unsorted Bool)))
;                (mvalid
;                  (mforall_prop
;                    (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
;                      (mforall_prop
;                        (lambda ((B (-> $$unsorted Bool)) (W $$unsorted))
;                          (mimplies
;                            (lambda ((W $$unsorted)) (forall ((V $$unsorted)) (or (not (R W V)) (or (A V) (B V))) ))
;                            (lambda
;                              ((W $$unsorted))
;                              (or
;                                (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
;                                (forall ((V $$unsorted)) (or (not (R W V)) (B V)) )))
;                            W))
;                        W)))) )))

(check-sat)
