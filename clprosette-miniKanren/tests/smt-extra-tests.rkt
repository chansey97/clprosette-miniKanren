#lang racket
(require "./mk.rkt")
(require "./test-check.rkt")
(printf "smt-extra-tests.rkt\n")

(test "conde"
      (run 3 (q)
           (smt-typeo q 'Int)
           (conde
            ((smt-asserto `(= ,q 1)))
            ((smt-asserto `(= ,q 2)))))
      '(1 2))

(test "join"
      (run 2 (q)
           (fresh (a b)
                  (== q `(,a ,b))
                  (conde
                   ((== a 4))
                   ((== a 2)))
                  (smt-typeo a 'Int)
                  (smt-typeo b 'Int)
                  (smt-asserto `(= ,a (+ ,b ,b)))))
      '((4 2) (2 1)))

(test "unif"
      (run 2 (q)
           (fresh (a b)
                  (== q `(,a ,b))
                  (smt-typeo a 'Int)
                  (smt-asserto `(> ,a 0))
                  (== b 2)
                  (== b a)))
      '((2 2)))

(test "unif2"
      (run 2 (q)
           (fresh (a b)
                  (== q `(,a ,b))
                  (smt-typeo a 'Int)
                  (smt-asserto `(> ,a 0))
                  (== b a)
                  (== b 2)))
      '((2 2)))

(define faco
  (lambda (n out)
    (fresh ()
           (smt-typeo n 'Int)
           (smt-typeo out 'Int)
           (conde ((smt-asserto `(= ,n 0))
                   (smt-asserto `(= ,out 1)))
                  ((smt-asserto `(> ,n 0))
                   (fresh (n-1 r)
                          (smt-typeo n-1 'Int)
                          (smt-typeo r 'Int)
                          (smt-asserto `(= (- ,n 1) ,n-1))
                          (smt-asserto `(= (* ,n ,r) ,out))
                          (faco n-1 r)))))))

;; equivalent
(define facto
  (lambda (n out)
    (conde ((== n 0)
            (== out 1))
           ((smt-typeo n 'Int)
            (smt-asserto `(> ,n 0))
            (fresh (n-1 r)
                   (smt-typeo n-1 'Int)
                   (smt-typeo r 'Int)
                   (smt-typeo out 'Int)
                   (smt-asserto `(= (- ,n 1) ,n-1))
                   (smt-asserto `(= (* ,n ,r) ,out))
                   (facto n-1 r))))))

(test "faco-0"
      (run* (q)
            (fresh (out)
                   (faco 0 out)
                   (== q out)))
      '(1))

(test "faco-1"
      (run* (q)
            (fresh (out)
                   (faco 1 out)
                   (== q out)))
      '(1))

(run 7 (q)
     (fresh (n out)
            (faco n out)
            (== q `(,n ,out))))

(run 7 (q)
     (fresh (n out)
            (facto n out)
            (== q `(,n ,out))))

(require "full-interp-with-let.rkt")
(test "evalo-backwards-fib-quoted-6"
  (run 1 (q)
    (evalo `(letrec ((f
                      (lambda (n)
                        (if (< n 0) #f
                            (if (< n 2) n
                                (+ (f (- n 1)) (f (- n 2))))))))
              (f ',q))
           8))
  '(6))

(test "fail-1"
      (run 1 (x)
           (=/= x 2)
           (smt-typeo x 'Int)
           (smt-asserto `(> ,x 1))
           (smt-asserto `(< ,x 3)))
      '())

(test "fail-2"
      (run 1 (x)
           (absento 2 x)
           (smt-typeo x 'Int)
           (smt-asserto `(> ,x 1))
           (smt-asserto `(< ,x 3)))
      '())

(test "fail-3"
      (run 2 (x)
           (=/= x 2)
           (smt-typeo x 'Int)
           (smt-asserto `(= 4 (* ,x ,x))))
      '(-2))

(test "real-1"
      (run 1 (x)
           (smt-typeo x 'Real)
           (smt-asserto `(= 4.2 (* 2 ,x))))
      '(2.1))

(test "diseq-0"
      (run 1 (q)
           (fresh (x y)
                  (smt-typeo x 'Int)
                  (smt-typeo y 'Int)
                  (smt-typeo q 'Int)
                  (smt-asserto `(> ,x 0))
                  (smt-asserto `(> ,y 0))
                  (smt-asserto `(= ,q (* ,x ,y)))))
      '(1))

(test "diseq-1"
      (run 1 (q)
           (fresh (x y)
                  (=/= x 0)
                  (=/= y 0)
                  (smt-typeo x 'Int)
                  (smt-typeo y 'Int)
                  (smt-typeo q 'Int)
                  (smt-asserto `(>= ,x 0))
                  (smt-asserto `(>= ,y 0))
                  (smt-asserto `(= ,q (* ,x ,y)))))
      '(1))


(test "diseq-2"
      (run 1 (q)
           (fresh (x y)
                  (smt-typeo x 'Int)
                  (smt-typeo y 'Int)
                  (smt-typeo q 'Int)
                  (smt-asserto `(>= ,x 0))
                  (smt-asserto `(>= ,y 0))
                  (smt-asserto `(= ,q (* ,x ,y)))
                  (=/= x 0)
                  (=/= y 0)))
      '(1))

(test "diseq-3"
      (run 1 (q)
           (fresh (x y)
                  (=/= x 0)
                  (=/= y 0)
                  (smt-typeo x 'Int)
                  (smt-typeo y 'Int)
                  (smt-asserto `(= 0 (* ,x ,y)))))
      '())

(test "diseq-4"
      (run 1 (q)
           (fresh (x y)
                  (smt-typeo x 'Int)
                  (smt-typeo y 'Int)
                  (smt-asserto `(= 0 (* ,x ,y)))
                  (=/= x 0)
                  (=/= y 0)))
      '())
