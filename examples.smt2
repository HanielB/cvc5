; ./debug/bin/cvc4 bug-scope.smt2 -t pnm-scope --dag-thresh=0 -t tepg-debug -t smt-proof --proof-print-conclusion -t pfcheck -t test --dump-proof -t pnm --proof-granularity=off -t pf-process-debug &> bug2.txt

; wrong
(= (f1$ x1$ x7$) (f1$ x8$ x6$))

(= (f1$ x8$ x6$) (f1$ x1$ x7$))

(SCOPE |:conclusion| (=> (and
                           (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$)))
                           (= (f1$ x1$ x7$) (f2$ x2$ x4$))
                           (= (f1$ x8$ x6$) (f1$ x1$ x7$))
                           (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))) (and (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$)))))
  (AND_INTRO |:conclusion| (and (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))))
    (SYMM |:conclusion| (= (f1$ x8$ x6$) (f1$ x1$ x7$))
      (ASSUME |:conclusion| (= (f1$ x1$ x7$) (f1$ x8$ x6$)) |:args| ((= (f1$ x1$ x7$) (f1$ x8$ x6$)))))
    (ASSUME |:conclusion| (= (f1$ x1$ x7$) (f2$ x2$ x4$)) |:args| ((= (f1$ x1$ x7$) (f2$ x2$ x4$))))
    (SYMM |:conclusion| (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))
      (ASSUME |:conclusion| (= (f2$ x2$ x4$) (f2$ (f5a$ x9$ x10$) x3$)) |:args| ((= (f2$ x2$ x4$) (f2$ (f5a$ x9$ x10$) x3$)))))
    (ASSUME |:conclusion| (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) |:args| ((not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))))))
  |:args| (
            (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$)))
            (= (f1$ x1$ x7$) (f2$ x2$ x4$))
            (= (f1$ x8$ x6$) (f1$ x1$ x7$))
            (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))))

; at theory engine proof generator
(SCOPE |:conclusion| (=> (and (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))) (and (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$)))))
  (AND_INTRO |:conclusion| (and (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))))
    (ASSUME |:conclusion| (= (f1$ x8$ x6$) (f1$ x1$ x7$)) |:args| ((= (f1$ x8$ x6$) (f1$ x1$ x7$))))
    (ASSUME |:conclusion| (= (f1$ x1$ x7$) (f2$ x2$ x4$)) |:args| ((= (f1$ x1$ x7$) (f2$ x2$ x4$))))
    (ASSUME |:conclusion| (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) |:args| ((= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))))
    (ASSUME |:conclusion| (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) |:args| ((not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))))))
  |:args| ((not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))))

; in update
(SCOPE |:conclusion| (=> (and (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))) (and (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$)))))
  (AND_INTRO |:conclusion| (and (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))))
    (ASSUME |:conclusion| (= (f1$ x8$ x6$) (f1$ x1$ x7$)) |:args| ((= (f1$ x8$ x6$) (f1$ x1$ x7$))))
    (ASSUME |:conclusion| (= (f1$ x1$ x7$) (f2$ x2$ x4$)) |:args| ((= (f1$ x1$ x7$) (f2$ x2$ x4$))))
    (ASSUME |:conclusion| (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$)) |:args| ((= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))))
    (ASSUME |:conclusion| (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) |:args| ((not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))))))
  |:args| ((not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$))) (= (f1$ x1$ x7$) (f2$ x2$ x4$)) (= (f1$ x8$ x6$) (f1$ x1$ x7$)) (= (f2$ (f5a$ x9$ x10$) x3$) (f2$ x2$ x4$))))


; all assumptions in final proof:
|:args| (
          (forall ((?v0 A$)) (not (= (f3$ x3$ ?v0) (f4$ (f5$ (f6$ ?v0) (f7$ ?v0)) (f8$ ?v0)))))
          (forall ((?v0 A$)) (not (= (f3$ x4$ ?v0) (f4$ x5$ (f9$ ?v0)))))
          (forall ((?v0 A$) (?v1 H$)) (not (= (f3a$ (f8$ ?v0) ?v1) (f3b$ x6$ (f10$ ?v1 ?v0)))))
          (forall ((?v0 A$) (?v1 H$)) (not (= (f3a$ (f9$ ?v0) ?v1) (f3b$ x7$ (f10$ ?v1 ?v0)))))
          (not (= (f1$ x8$ x6$) (f2$ (f5a$ x9$ x10$) x3$)))
          (= (f1$ x1$ x7$) (f1$ x8$ x6$))
          (= (f1$ x1$ x7$) (f2$ x2$ x4$))
          (= (f2$ x2$ x4$) (f2$ (f5a$ x9$ x10$) x3$))
          (not false))
