(set-logic LIRA)
;;(set-feature :fwd-decls true)
(synth-fun sygus.qi-aux ((vmt.x Int) (vmt.f Bool)) Bool)
(synth-fun sygus.inv ((vmt.x Int) (vmt.f Bool)) Bool)
(synth-fun sygus.rf ((sygus.idx Int) (vmt.x Int) (vmt.f Bool)) Int)
(define-fun sygus.lin-rf-conds
  ((sygus.idx Int) (vmt.x Int) (vmt.f Bool) (vmt.x.next Int) (vmt.f.next Bool)) Bool
  (and (>= (sygus.rf sygus.idx vmt.x vmt.f) 0)
    (> (sygus.rf sygus.idx vmt.x vmt.f) (sygus.rf sygus.idx vmt.x.next vmt.f.next)))
)
(define-fun sygus.lin-rf-conds-aux
  ((sygus.idx Int) (vmt.x Int) (vmt.f Bool) (vmt.x.next Int) (vmt.f.next Bool) (sygus.pred Bool)) Bool
  (or (sygus.lin-rf-conds sygus.idx vmt.x vmt.f vmt.x.next vmt.f.next)
    (and (>= (sygus.rf sygus.idx vmt.x vmt.f) (sygus.rf sygus.idx vmt.x.next vmt.f.next)) sygus.pred))
)
(synth-fun sygus.lex-rf-conds
  ((vmt.x Int) (vmt.f Bool) (vmt.x.next Int) (vmt.f.next Bool)) Bool
  ;;((S Bool))
  ;;((S Bool (
  ;;   (sygus.lin-rf-conds 0 vmt.x vmt.f vmt.x.next vmt.f.next)
  ;;   (sygus.lin-rf-conds-aux (Constant Int) vmt.x vmt.f vmt.x.next vmt.f.next S)
  ;; )))
  ((Start Bool (
    (sygus.lin-rf-conds 0 vmt.x vmt.f vmt.x.next vmt.f.next)
    (sygus.lin-rf-conds-aux (Constant Int) vmt.x vmt.f vmt.x.next vmt.f.next Start)
  )))
)
(declare-var vmt.x Int)
(declare-var vmt.x.next Int)
(declare-var vmt.f Bool)
(declare-var vmt.f.next Bool)
(define-fun vmt.s0 () Int vmt.x)
(define-fun vmt.s1 () Bool vmt.f)
(define-fun vmt.init () Bool (and (> vmt.x 0) (not vmt.f)))
(define-fun vmt.trans () Bool
 (and
  (or (and (= vmt.x 0) (= vmt.x.next vmt.x) (not vmt.f.next))
   (and (not (= vmt.x 0)) (= vmt.x.next (- vmt.x 1)) vmt.f.next))))
(define-fun sygus.qi ((vmt.x Int) (vmt.f Bool)) Bool
 (and (sygus.qi-aux vmt.x vmt.f) (not vmt.f)))
(constraint
 (and (=> vmt.init (sygus.inv vmt.x vmt.f))
  (=> (and (sygus.inv vmt.x vmt.f) vmt.trans)
   (sygus.inv vmt.x.next vmt.f.next))))
(constraint
 (=> (and (sygus.qi vmt.x vmt.f) vmt.trans) (sygus.qi vmt.x.next vmt.f.next)))
(constraint
 (=> (and (not (sygus.qi vmt.x vmt.f)) vmt.trans (sygus.inv vmt.x vmt.f))
  (or (sygus.qi vmt.x.next vmt.f.next)
    (sygus.lex-rf-conds vmt.x vmt.f vmt.x.next vmt.f.next)
   )))
(check-synth)