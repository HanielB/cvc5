(set-option :incremental false)
(set-logic ALL)
(declare-sort $$unsorted 0)
(declare-sort produc1516857811k_elem 0)
(declare-sort var 0)
(declare-fun transi803447880k_elem ((-> produc1516857811k_elem produc1516857811k_elem Bool) produc1516857811k_elem produc1516857811k_elem) Bool)

(assert (forall ((R (-> produc1516857811k_elem produc1516857811k_elem Bool))) (= (transi803447880k_elem (transi803447880k_elem R)) (transi803447880k_elem R)) ))

(assert
  (= transi803447880k_elem
    (lambda ((R4 (-> produc1516857811k_elem produc1516857811k_elem Bool)) (__flatten_var_0 produc1516857811k_elem) (__flatten_var_1 produc1516857811k_elem))
      ((lambda ((A12 produc1516857811k_elem) (__flatten_var_0 produc1516857811k_elem))
         ((lambda ((A23 produc1516857811k_elem))
            (or
              (exists ((A5 produc1516857811k_elem))
                (and (= A12 A5) (= A23 A5)) )
              (exists ((A5 produc1516857811k_elem))
                (exists ((B4 produc1516857811k_elem))
                  (exists ((C5 produc1516857811k_elem))
                    (and
                      (= A12 A5)
                      (and
                        (= A23 C5)
                        (and
                          (transi803447880k_elem R4 A5 B4)
                          (R4 B4 C5)))) ) ) )))
           __flatten_var_0))
        __flatten_var_0 __flatten_var_1))))

(check-sat)
