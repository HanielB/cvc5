(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
; (set-info :status unsat)
(declare-sort U 0)
(declare-fun f1 () U)
(declare-fun f2 () U)
(declare-fun f3 () U)
(declare-fun f4 () U)
(declare-fun p (U) Bool)
(assert (not (= f1 f2)))
(assert (and (p f1) (or (= f1 f2) (distinct f3 f4 f2)) (p f3)))
(assert (= f3 f4))
(check-sat)
(exit)


;; reminder:

; (assert (not (= f1 f2)))
; (assert (not (distinct f3 f4 f2)))
; (assert (not (= f3 f4)))

; with different sorts for {f1,f2} and {f3,f4} gives

; "(error "smt2_term_app: unresolved symbol distinct on line 126.")"

; when it should actually be a typing error

;; another reminder 

; (declare-fun p (U) U)
; (assert (not (= f1 f2)))
; (assert (and (p f1) (or (= f1 f2) (distinct f3 f4 f2)) (p f3)))
; (assert (= f3 f4))

; leads to assertion error

; veriT: src/symbolic/DAG-sort-pm.c:244: DAG_sort_unif_solve: Assertion
; `DAG_sort_arity(sort1) > 0' failed.

; instead of type error
