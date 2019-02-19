(set-logic ALL)
(declare-sort $$unsorted 0)

(declare-fun mvalid ((-> $$unsorted Bool)) Bool)
(assert (= mvalid (lambda ((Phi (-> $$unsorted Bool))) (forall ((W $$unsorted)) (Phi W) ))))

(declare-fun mforall_prop ((-> (-> $$unsorted Bool) $$unsorted Bool) $$unsorted) Bool)
(assert (= mforall_prop
          (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
            (forall ((P (-> $$unsorted Bool))) (Phi P W) ))))

(declare-fun mnot ((-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mnot (lambda ((Phi (-> $$unsorted Bool)) (W $$unsorted)) (not (Phi W)))))

(declare-fun mor ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mor
          (lambda ((Phi (-> $$unsorted Bool)) (Psi (-> $$unsorted Bool)) (W $$unsorted))
            (or (Phi W) (Psi W)))))

(declare-fun mimplies ((-> $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mimplies
          (lambda (
                    (Phi (-> $$unsorted Bool))
                    (Psi (-> $$unsorted Bool)) (W $$unsorted))
            (mor (mnot Phi) Psi W))))

(declare-fun mbox ((-> $$unsorted $$unsorted Bool) (-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mbox
          (lambda ((R (-> $$unsorted $$unsorted Bool)) (Phi (-> $$unsorted Bool)) (W $$unsorted))
            (forall ((V $$unsorted)) (or (not (R W V)) (Phi V)) ))))


;;;;;;;;;;;; unknown here

; (assert (not (forall ((R (-> $$unsorted $$unsorted Bool)))
;                (forall ((W $$unsorted))
;                  (mforall_prop
;                    (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
;                      (forall ((P (-> $$unsorted Bool)))
;                        (or (not (forall ((V $$unsorted))
;                                   (or (not (R W V)) (or (A V) (P V)))))
;                          (or
;                            (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
;                            (forall ((V $$unsorted)) (or (not (R W V)) (P V)) )
;                            )
;                          )
;                        )
;                      )
;                    W
;                    )
;                  )
;                )
;           )
;   )


;;;;;;;;;;; unsat up to here

(assert
  (not (forall ((R (-> $$unsorted $$unsorted Bool)))
         (forall ((W $$unsorted))
           (mforall_prop
             (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
               (mforall_prop
                 (lambda ((B (-> $$unsorted Bool)) (W $$unsorted))
                   (or
                     (not (forall ((V $$unsorted)) (or (not (R W V)) (or (A V) (B V))) ))
                     (or
                       (forall ((V $$unsorted)) (or (not (R W V)) (A V)))
                       (forall ((V $$unsorted)) (or (not (R W V)) (B V)))
                       )
                     )
                   )
                 W)
               )
             W)
           )
         )
    )
  )




; +++++++++++++++++++++

;;; init:

(not
  (forall ((R (-> $$unsorted $$unsorted Bool)) (W $$unsorted))
    (mforall_prop
      (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
        (mforall_prop
          (lambda ((B (-> $$unsorted Bool)) (W $$unsorted))
            (or
              (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (B V)) ))
              (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
              (forall ((V $$unsorted)) (or (not (R W V)) (B V)) )))
          W))
      W) ))

;;; after sub

(not
  (forall ((R (-> $$unsorted $$unsorted Bool)) (W $$unsorted))
    (
      (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
        (forall ((P (-> $$unsorted Bool))) (Phi P W) ))
      (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
        (
          (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
            (forall ((P (-> $$unsorted Bool))) (Phi P W) ))
          (lambda ((B (-> $$unsorted Bool)) (W $$unsorted))
            (or
              (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (B V)) ))
              (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
              (forall ((V $$unsorted)) (or (not (R W V)) (B V)) )))
          W))
      W) ))


;;;; 1st beta

(not
  (forall ((R (-> $$unsorted $$unsorted Bool)) (W $$unsorted))
    (
      (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
        (forall ((P (-> $$unsorted Bool))) (Phi P W) ))
      (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
        (forall ((P (-> $$unsorted Bool)))
          (
            (lambda ((B (-> $$unsorted Bool)) (W $$unsorted))
              (or
                (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (B V)) ))
                (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
                (forall ((V $$unsorted)) (or (not (R W V)) (B V)) )))
            P W) )
        )
      W) ))


;;;;; 2nd beta

(not
  (forall ((R (-> $$unsorted $$unsorted Bool)) (W $$unsorted))
    (
      (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
        (forall ((P (-> $$unsorted Bool))) (Phi P W) ))
      (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
        (forall ((P (-> $$unsorted Bool)))
          (or
            (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (P V)) ))
            (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
            (forall ((V $$unsorted)) (or (not (R W V)) (P V)) ))
          )
        )
      W) ))


; rewrite internally to
(or
  (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
  (forall ((P (-> $$unsorted Bool))) (or (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (P V)) )) (forall ((V $$unsorted)) (or (not (R W V)) (P V)) )) ))

;; rewrite internally the second disjunct of the above to
(forall ((P (-> $$unsorted Bool)) (BOUND_VARIABLE_470 $$unsorted)) (or (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (P V)) )) (or (not (R W BOUND_VARIABLE_470)) (P BOUND_VARIABLE_470))) )

(
  (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted)) (forall ((P (-> $$unsorted Bool))) (Phi P W) ))
  (lambda ((B (-> $$unsorted Bool)) (W $$unsorted)) (or (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (B V)) )) (forall ((V $$unsorted)) (or (not (R W V)) (A V)) ) (forall ((V $$unsorted)) (or (not (R W V)) (B V)) )))
  W)
; to
(or (forall ((V $$unsorted)) (or (not (R W V)) (A V)) ) (forall ((P (-> $$unsorted Bool)) (BOUND_VARIABLE_470 $$unsorted)) (or (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (P V)) )) (not (R W BOUND_VARIABLE_470)) (P BOUND_VARIABLE_470)) ))

;;;;; 3rd beta

(
  (lambda ((Phi (-> (-> $$unsorted Bool) $$unsorted Bool)) (W $$unsorted))
    (forall ((P (-> $$unsorted Bool))) (Phi P W) ))
  (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
    (or
      (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
      (forall ((P (-> $$unsorted Bool)) (BOUND_VARIABLE_470 $$unsorted))
        (or
          (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (P V)) ))
          (not (R W BOUND_VARIABLE_470)) (P BOUND_VARIABLE_470)) )))
  W)

; into

(forall ((P (-> $$unsorted Bool)))
  (
    (lambda ((A (-> $$unsorted Bool)) (W $$unsorted))
      (or
        (forall ((V $$unsorted)) (or (not (R W V)) (A V)) )
        (forall ((P (-> $$unsorted Bool)) (BOUND_VARIABLE_470 $$unsorted))
          (or
            (not (forall ((V $$unsorted)) (or (not (R W V)) (A V) (P V)) ))
            (not (R W BOUND_VARIABLE_470)) (P BOUND_VARIABLE_470)) )))
    P W) )

;;;;;;; 4rth beta

(or
  (forall ((V $$unsorted)) (or (not (R W V)) (P V)) )
  (forall ((P (-> $$unsorted Bool)) (BOUND_VARIABLE_470 $$unsorted))
    (or
      (not (forall ((V $$unsorted)) (or (not (R W V)) ([P CAPTUREEEEEEEEEEEEEEEEEEEEEEEEEED] V) (P V)) ))
      (not (R W BOUND_VARIABLE_470)) (P BOUND_VARIABLE_470)) ))


;;;;;;;; result

; (not
;   (forall (
;             (R (-> $$unsorted $$unsorted Bool))
;             (W $$unsorted)
;             (BOUND_VARIABLE_536 $$unsorted)
;             (BOUND_VARIABLE_537 (-> $$unsorted Bool))
;             (BOUND_VARIABLE_542 (-> $$unsorted Bool))
;             (BOUND_VARIABLE_543 $$unsorted))
;     (or
;       (not (R W BOUND_VARIABLE_536))
;       (BOUND_VARIABLE_537 BOUND_VARIABLE_536)
;       (not
;         (forall ((V $$unsorted))
;           (or
;             (not (R W V))
;             (BOUND_VARIABLE_542 V)) ))
;       (not (R W BOUND_VARIABLE_543))
;       (BOUND_VARIABLE_542 BOUND_VARIABLE_543)) ))


(check-sat)