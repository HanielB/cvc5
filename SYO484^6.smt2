(set-option :incremental false)
(set-logic ALL)
(declare-sort $$unsorted 0)
(declare-sort mu 0)

(declare-fun meq_ind (mu mu $$unsorted) Bool)
(assert (= meq_ind (lambda ((X mu) (Y mu) (W $$unsorted)) (= X Y))))

(declare-fun mforall_ind ((-> mu $$unsorted Bool) $$unsorted) Bool)
(assert (= mforall_ind (lambda ((Phi (-> mu $$unsorted Bool)) (W $$unsorted)) (forall ((X mu)) (Phi X W) ))))

(declare-fun mreflexive ((-> $$unsorted $$unsorted Bool)) Bool)
(assert (= mreflexive (lambda ((R (-> $$unsorted $$unsorted Bool))) (forall ((S $$unsorted)) (R S S) ))))

(declare-fun msymmetric ((-> $$unsorted $$unsorted Bool)) Bool)
(assert (= msymmetric (lambda ((R (-> $$unsorted $$unsorted Bool))) (forall ((S $$unsorted) (T $$unsorted)) (=> (R S T) (R T S)) ))))


(declare-fun mtransitive ((-> $$unsorted $$unsorted Bool)) Bool)
(assert (= mtransitive (lambda ((R (-> $$unsorted $$unsorted Bool))) (forall ((S $$unsorted) (T $$unsorted) (U $$unsorted)) (=> (and (R S T) (R T U)) (R S U)) ))))



(declare-fun mvalid ((-> $$unsorted Bool)) Bool)
(assert (= mvalid (lambda ((Phi (-> $$unsorted Bool))) (forall ((W $$unsorted)) (Phi W) ))))


(declare-fun rel_s5 ($$unsorted $$unsorted) Bool)
(declare-fun mbox_s5 ((-> $$unsorted Bool) $$unsorted) Bool)
(assert (= mbox_s5 (lambda ((Phi (-> $$unsorted Bool)) (W $$unsorted)) (forall ((V $$unsorted)) (or (not (rel_s5 W V)) (Phi V)) ))))

(assert (mreflexive rel_s5))
(assert (mtransitive rel_s5))
(assert (msymmetric rel_s5))
(assert (not (mvalid (mforall_ind (lambda ((X mu) (__flatten_var_0 $$unsorted)) (mbox_s5 (mforall_ind (lambda ((Y mu) (__flatten_var_0 $$unsorted)) (meq_ind X Y __flatten_var_0))) __flatten_var_0))))))

(check-sat)
