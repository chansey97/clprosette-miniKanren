#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
(require "../test-check.rkt")
(require "../logging.rkt")
(printf "clpsmt-basic-tests.rkt\n")

;; mock
(define z3-counter-check-sat 0)
(define z3-counter-get-model 0)

(test "counters"
  (let ((c1 z3-counter-check-sat)
        (c2 z3-counter-get-model))
    (run* (q)
      (rosette-typeo q r/@integer?)
      (rosette-asserto `(,r/@= ,q 0)))
    (list
     (- z3-counter-check-sat c1)
     (- z3-counter-get-model c2)))
  '(4 1))

(test "declare-idempotent"
  (run* (q)
    (fresh (v1 v2)
      (rosette-typeo v1 r/@boolean?)
      (rosette-typeo v2 r/@boolean?)
      (== v1 v2)
      (== q v1)))
  '(#f #t))

(test "inf-smt-ans-1"
  (run 1 (q)
    (rosette-typeo q r/@integer?)
    (rosette-asserto `(,r/@>= ,q 0)))
  '(0))

(test "inf-smt-ans-2"
  (run 2 (q)
    (rosette-typeo q r/@integer?)
    (rosette-asserto `(,r/@>= ,q 0)))
  '(0 1))

(test "1"
  (run* (q)
    (fresh (x)
      (rosette-typeo x r/@integer?)
      (rosette-asserto `(,r/@= ,x 0))))
  '(_.0))

(test "2"
  (run* (q)
    (fresh (x)
      (rosette-typeo x r/@integer?)
      (rosette-asserto `(,r/@= ,x 0))
      (rosette-asserto `(,r/@= ,x 1))))
  '())

(test "3"
  (run* (q)
    (fresh (x)
      (rosette-typeo x r/@integer?)
      (rosette-asserto `(,r/@= ,x 0))
      (== x q)))
  '(0))

(test "4"
  (run* (q)
    (rosette-typeo q r/@integer?)
    (rosette-asserto `(,r/@= ,q 0)))
  '(0))

(test "5"
  (run 2 (f)
    (rosette-typeo f (r/~> r/@integer? r/@integer?))
    (rosette-asserto `(,r/@= 1 (,f 1)))
    (rosette-asserto `(,r/@= 0 (,f 0))))
  ;; what do we really want here? syntax lambda or actual lambda?
  ;; In clprosette, it is actual lambda!
  '((lambda (x!0) (ite (= x!0 1) 1 (ite (= x!0 0) 0 1)))))

(test "6"
  (run 1 (q)
    (fresh (f x)
      (rosette-typeo x r/@integer?)
      (rosette-typeo f (r/~> r/@integer? r/@integer?))
      (rosette-asserto `(,r/@= ,x (,f ,x)))
      (== q x)))
  '(0))
