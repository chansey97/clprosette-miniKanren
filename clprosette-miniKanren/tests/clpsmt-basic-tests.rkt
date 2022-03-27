(test "counters"
      (let ((c1 z3-counter-check-sat)
            (c2 z3-counter-get-model))
        (run* (q)
              (smt-typeo q 'Int)
              (smt-asserto `(= ,q 0)))
        (list
         (- z3-counter-check-sat c1)
         (- z3-counter-get-model c2)))
      '(4 1))

(test "declare-idempotent"
      (run* (q)
            (fresh (v1 v2)
                   (smt-typeo v1 'Bool)
                   (smt-typeo v2 'Bool)
                   (== v1 v2)
                   (== q v1)))
      '(#f #t))

(test "inf-smt-ans-1"
      (run 1 (q)
           (smt-typeo q 'Int)
           (smt-asserto `(>= ,q 0)))
      '(0))

(test "inf-smt-ans-2"
      (run 2 (q)
           (smt-typeo q 'Int)
           (smt-asserto `(>= ,q 0)))
      '(0 1))

(test "1"
      (run* (q)
            (fresh (x)
                   (smt-typeo x 'Int)
                   (smt-asserto `(= ,x 0))))
      '(_.0))

(test "2"
      (run* (q)
            (fresh (x)
                   (smt-typeo x 'Int)
                   (smt-asserto `(= ,x 0))
                   (smt-asserto `(= ,x 1))))
      '())

(test "3"
      (run* (q)
            (fresh (x)
                   (smt-typeo x 'Int)
                   (smt-asserto `(= ,x 0))
                   (== x q)))
      '(0))

(test "4"
      (run* (q)
            (smt-typeo q 'Int)
            (smt-asserto `(= ,q 0)))
      '(0))

;; TODO: Support other types

;; (test "5"
;;       (run 2 (f)
;;            (smt-typeo f '(-> Int Int))
;;            (smt-asserto `(= 1 (,f 1)))
;;            (smt-asserto `(= 0 (,f 0))))
;;       ;; TODO:
;;       ;; what do we really want here? syntax lambda or actual lambda?
;;       '((lambda (x!0) (ite (= x!0 1) 1 (ite (= x!0 0) 0 1)))))

;; (test "6"
;;       (run 1 (q)
;;            (fresh (f x)
;;                   (smt-typeo f '(-> Int Int))
;;                   (smt-asserto `(= ,x (,f ,x)))
;;                   (== q x)))
;;       '(0))
