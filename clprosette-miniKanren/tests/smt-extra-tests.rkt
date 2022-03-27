#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
(require "../test-check.rkt")
(printf "smt-extra-tests.rkt\n")

(test "conde"
  (run 3 (q)
    (rosette-typeo q r/@integer?)
    (conde
      ((rosette-asserto `(,r/@= ,q 1)))
      ((rosette-asserto `(,r/@= ,q 2)))))
  '(1 2))

(test "join"
  (run 2 (q)
    (fresh (a b)
      (== q `(,a ,b))
      (conde
        ((== a 4))
        ((== a 2)))
      (rosette-typeo a r/@integer?)
      (rosette-typeo b r/@integer?)
      (rosette-asserto `(,r/@= ,a (,r/@+ ,b ,b)))))
  '((4 2) (2 1)))

(test "unif"
  (run 2 (q)
    (fresh (a b)
      (== q `(,a ,b))
      (rosette-typeo a r/@integer?)
      (rosette-asserto `(,r/@> ,a 0))
      (== b 2)
      (== b a)))
  '((2 2)))

(test "unif2"
  (run 2 (q)
    (fresh (a b)
      (== q `(,a ,b))
      (rosette-typeo a r/@integer?)
      (rosette-asserto `(,r/@> ,a 0))
      (== b a)
      (== b 2)))
  '((2 2)))

(define faco
  (lambda (n out)
    (fresh ()
      (rosette-typeo n r/@integer?)
      (rosette-typeo out r/@integer?)
      (conde ((rosette-asserto `(,r/@= ,n 0))
              (rosette-asserto `(,r/@= ,out 1)))
             ((rosette-asserto `(,r/@> ,n 0))
              (fresh (n-1 r)
                (rosette-typeo n-1 r/@integer?)
                (rosette-typeo r r/@integer?)
                (rosette-asserto `(,r/@= (,r/@- ,n 1) ,n-1))
                (rosette-asserto `(,r/@= (,r/@* ,n ,r) ,out))
                (faco n-1 r)))))))

;; equivalent
(define facto
  (lambda (n out)
    (conde ((== n 0)
            (== out 1))
           ((rosette-typeo n r/@integer?)
            (rosette-asserto `(,r/@> ,n 0))
            (fresh (n-1 r)
              (rosette-typeo n-1 r/@integer?)
              (rosette-typeo r r/@integer?)
              (rosette-typeo out r/@integer?)
              (rosette-asserto `(,r/@= (,r/@- ,n 1) ,n-1))
              (rosette-asserto `(,r/@= (,r/@* ,n ,r) ,out))
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
    (rosette-typeo x r/@integer?)
    (rosette-asserto `(,r/@> ,x 1))
    (rosette-asserto `(,r/@< ,x 3)))
  '())

(test "fail-2"
  (run 1 (x)
    (absento 2 x)
    (rosette-typeo x r/@integer?)
    (rosette-asserto `(,r/@> ,x 1))
    (rosette-asserto `(,r/@< ,x 3)))
  '())

(test "fail-3"
  (run 2 (x)
    (=/= x 2)
    (rosette-typeo x r/@integer?)
    (rosette-asserto `(,r/@= 4 (,r/@* ,x ,x))))
  '(-2))

(test "real-1"
  (run 1 (x)
    (rosette-typeo x r/@real?)
    (rosette-asserto `(,r/@= 4.2 (,r/@* 2 ,x))))
  '(2.1))

(test "diseq-0"
  (run 1 (q)
    (fresh (x y)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-typeo q r/@integer?)
      (rosette-asserto `(,r/@> ,x 0))
      (rosette-asserto `(,r/@> ,y 0))
      (rosette-asserto `(,r/@= ,q (,r/@* ,x ,y)))))
  '(1))

(test "diseq-1"
  (run 1 (q)
    (fresh (x y)
      (=/= x 0)
      (=/= y 0)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-typeo q r/@integer?)
      (rosette-asserto `(,r/@>= ,x 0))
      (rosette-asserto `(,r/@>= ,y 0))
      (rosette-asserto `(,r/@= ,q (,r/@* ,x ,y)))))
  '(1))


(test "diseq-2"
  (run 1 (q)
    (fresh (x y)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-typeo q r/@integer?)
      (rosette-asserto `(,r/@>= ,x 0))
      (rosette-asserto `(,r/@>= ,y 0))
      (rosette-asserto `(,r/@= ,q (,r/@* ,x ,y)))
      (=/= x 0)
      (=/= y 0)))
  '(1))

(test "diseq-3"
  (run 1 (q)
    (fresh (x y)
      (=/= x 0)
      (=/= y 0)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-asserto `(,r/@= 0 (,r/@* ,x ,y)))))
  '())

(test "diseq-4"
  (run 1 (q)
    (fresh (x y)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-asserto `(,r/@= 0 (,r/@* ,x ,y)))
      (=/= x 0)
      (=/= y 0)))
  '())
