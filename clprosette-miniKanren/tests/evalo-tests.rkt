#lang racket
(require "../mk.rkt")
(require "../test-check.rkt")
(require "../full-interp-extended.rkt")

(test "fac:"
  (run* (q)
    (evalo `(letrec ((fac
                      (lambda (n)
                        (if (< n 0)
                            #f
                            (if (= n 0)
                                1
                                (* n (fac (- n 1))))))))
              (fac 3))
           q))
  '(6))

(test "fac: synthesis expression"
  (run 1 (q)
    (evalo `(letrec ((fac
                      (lambda (n)
                        (if (< n 0)
                            #f
                            (if (= n ,q)
                                1
                                (* n (fac (- n 1))))))))
              (fac 3))
           6))
  '(1))

(test "fac: synthesis value"
  (run 1 (q)
    (evalo `(letrec ((fac
                      (lambda (n)
                        (if (< n 0)
                            #f
                            (if (= n ',q)
                                1
                                (* n (fac (- n 1))))))))
              (fac 3))
           6))
  '(1))

;; ok, but very slow...
;; (test "fib: synthesis value"
;;       (run 1 (q)
;;            (evalo `(letrec ((f
;;                              (lambda (n)
;;                                (if (< n 0) #f
;;                                    (if (< n 2) n
;;                                        (+ (f (- n 1)) (f (- n 2))))))))
;;                      (f ',q))
;;                   8))
;;       '(6))


(test "refutation example"
  (run 1 (q)
    (fresh (x y)
      (evalo `(and (not (equal? (list ',x 111)
                                (list 0 111))) 
                   (not (equal? (list ',y 222)
                                (list 0 222)))
                   (= 0 (* ',x ',y)))
             #t)
      ))
  '())

