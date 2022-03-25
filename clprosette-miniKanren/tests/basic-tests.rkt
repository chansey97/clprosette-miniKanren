#lang racket
(require "../../rosette/rosette/base/core/term.rkt")
(require "../../rosette/rosette/base/core/type.rkt")
(require "../../rosette/rosette/base/form/define.rkt")

(require "../../rosette/rosette/solver/solver.rkt")
(require "../../rosette/rosette/solver/solution.rkt")
(require "../../rosette/rosette/solver/smt/z3.rkt")
(require (only-in "../../rosette/rosette/solver/smt/server.rkt" output-smt))

(require (prefix-in r/ "../../rosette/rosette/base/core/equality.rkt"))
(require (prefix-in r/ "../../rosette/rosette/base/core/bool.rkt"))
(require (prefix-in r/ "../../rosette/rosette/base/core/real.rkt"))

(require "../../rosette/rosette/query/core.rkt") ; current-solver
;; (require "../../rosette/rosette/query/finitize.rkt")

(require "../logging.rkt")
(require "../test-check.rkt")
(require "../mk.rkt")

;; (current-bitwidth 8)
;; (output-smt #t)
(current-solver
 (z3
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

(test "rosette-typeo-without-assertion"
  (run 1 (q)
    (fresh ()
      (rosette-typeo q r/@integer?)
      ))
  '(0))

(test "rosette-typeo-without-assertion-2"
  (run 5 (q)
    (fresh (a b)
      (rosette-typeo a r/@integer?)
      (rosette-typeo b r/@integer?)
      (rosette-asserto `(,r/@>= ,b 0))
      (== q `(,a ,b))
      ))
  '((0 0) (-1 1) (-2 2) (1 0) (-3 0)))

(test "basic"
  (run 1 (q)
    (fresh ()
      (rosette-typeo q r/@integer?)
      (rosette-asserto `(,r/@equal? ,q 5))
      ))
  '(5))

(test "basic"
  (run 2 (q)
    (fresh ()
      (rosette-typeo q r/@integer?)
      (conde
        ((rosette-asserto `(,r/@equal? ,q 1)))
        ((rosette-asserto `(,r/@equal? ,q 2))))
      ))
  '(1 2))

(test "==-and-smt:"
  (run 1 (q)
    (fresh (a b)
      (== a b)
      (rosette-typeo a r/@integer?) ;
      (rosette-asserto `(,r/@equal? ,a 5))
      ))
  '(_.0))

(test "==-and-smt: duplicate declare"
  (run 1 (q)
    (fresh (a b)
      (== a b)
      (rosette-typeo a r/@integer?)
      (rosette-asserto `(,r/@equal? ,a 5))
      (rosette-typeo b r/@integer?)
      ))
  '(_.0))


(test "==-and-smt: fix a bug when gc-assumption-threshold = 1"
  (run 3 (q)
    (conde
      ((fresh (x)
         (rosette-typeo x r/@integer?)
         (rosette-asserto `(,r/@equal? ,x 1))))
      ((fresh (x)
         (rosette-typeo x r/@integer?)
         (rosette-asserto `(,r/@equal? ,x 2))))
      ))
  '(_.0 _.0))


(test "==-and-smt: duplicate declare in conde, and fix a bug when gc-assumption-threshold = 1"
  (run 3 (q)
    (conde
      ((rosette-typeo q r/@integer?)
       (rosette-asserto `(,r/@equal? ,q 1)))
      ((rosette-typeo q r/@integer?)
       (rosette-asserto `(,r/@equal? ,q 2)))
      ))
  '(1 2))


(test "boolean"
  (run 1 (q)
    (fresh (a b)
      (== a b)
      (rosette-typeo a r/@boolean?)
      (rosette-asserto `(,r/@equal? ,a #f))
      (== q `(,a ,b))))
  '((#f #f)))

(let ()

  ;; https://github.com/namin/clpsmt-miniKanren/issues/10

  ;; Declare a fresh variable at the top

  (define add1o
    (lambda (n out)
      (fresh ()
        (rosette-asserto `(,r/@= ,out (,r/@+ ,n 1))))))

  (test ""
    (run 5 (q)
      (fresh (n out)
        (rosette-typeo n r/@integer?)
        (rosette-typeo out r/@integer?)
        (add1o n out)
        (== q `(,n ,out))))
    '((0 1) (1 2) (2 3) (3 4) (4 5)))

  (test ""
    (run 5 (q)
      (fresh (n)
        (rosette-typeo n r/@integer?)
        (add1o n 1)
        (== q n)))
    '(0))

  (test ""
    (run 5 (q)
      (fresh (out)
        (rosette-typeo out r/@integer?)
        (add1o 1 out)
        (== q out)))
    '(2))
  )

(let ()
  ;; Declare a variable, but that variable has already been unified with a constant.
  (define add1o
    (lambda (n out)
      (fresh ()
        (rosette-typeo n r/@integer?)
        (rosette-typeo out r/@integer?)
        (rosette-asserto `(,r/@= ,out (,r/@+ ,n 1))))))

  (test ""
    (run 5 (q)
      (fresh (n out)
        (add1o n out)
        (== q `(,n ,out))))
    '((0 1) (-1 0) (-2 -1) (-3 -2) (-4 -3)))

  (test ""
    (run 5 (q)
      (fresh (n)
        (add1o n 1)
        (== q n)))
    '(0))
  )

(let ()
  (define (nevero)
    (conde
      [(== 1 2)]
      [(nevero)]))

  (test ""
    (run 1 (q)
      (fresh (a b)
        (rosette-typeo a r/@integer?)
        (rosette-asserto `(,r/@= ,a 5))

        (rosette-typeo b r/@integer?)
        (rosette-asserto `(,r/@= ,b 6))

        (== a b) ; <-- promote the `==` to SMT assert

        (nevero)))
    '())
  )

(let ()

  (define (nevero)
    (conde
      [(== 1 2)]
      [(nevero)]))

  (test ""
    (run 1 (q)
      (fresh (a b)
        (=/= a b)

        (rosette-typeo a r/@integer?)
        (rosette-asserto `(,r/@= ,a 5))

        (rosette-typeo b r/@integer?)
        (rosette-asserto `(,r/@= ,b 5)) ; <-- promote the above `=/=` to SMT assert

        (nevero)))
    '())

  (test ""
    (run 3 (q)
      (fresh (a b)
        (=/= a b)
        (rosette-typeo a r/@integer?)
        (rosette-asserto `(,r/@= ,a 5)) ; <-- won't actually promote the above `=/=` to SMT assert, because b is not a SMT variable
        (== q `(,a ,b))))
    '(((5 _.0) (=/= ((_.0 5))))))
  )




(let ()
  (define (nevero)
    (conde
      [(== 1 2)]
      [(nevero)]))

  (test ""
    (run 1 (q)
      (fresh (a b)

        (rosette-typeo a r/@integer?)
        (rosette-asserto `(,r/@= ,a 5))

        (rosette-typeo b r/@integer?)
        (rosette-asserto `(,r/@= ,b 5))

        (=/= a b) ; <-- promote the `=/=` to SMT assert 

        (nevero)))
    '())

  (test "refute"
    (run 1 (q)
      (fresh (a b)
        (=/= a b)
        (rosette-typeo a r/@integer?)
        (rosette-typeo b r/@integer?)
        (rosette-asserto `(,r/@= (,r/@- ,a ,b) 0))  ; <-- promote the above `=/=` to SMT assert 
        ))
    '())
  )

(let ()

  (define (nevero)
    (conde
      [(== 1 2)]
      [(nevero)]))

  (test ""
    (run 1 (q)
      (fresh (a b c d)
        (=/= (list a b) (list c d))

        (rosette-typeo a r/@integer?)
        (rosette-typeo c r/@integer?)
        (rosette-asserto `(,r/@< ,a 2))
        (rosette-asserto `(,r/@> ,a 0))
        (rosette-asserto `(,r/@= ,c 1))

        (== b d)

        (nevero)
        ))
    '())
  )


(test ""
  (run 3 (q)
    (fresh (a b c d e f)
      (=/= (list a b c) (list d e f))

      (rosette-typeo b r/@integer?)
      (rosette-typeo e r/@integer?)
      (rosette-asserto `(,r/@< ,b 2))
      (rosette-asserto `(,r/@> ,b 0))
      (rosette-asserto `(,r/@= ,e 1))

      (== a d)
      (== c f)
      ))
  '())

(test ""
  (run 3 (q)
    (fresh (a b c d e f)
      (=/= (list a b c) (list d e f))

      (rosette-typeo b r/@integer?)
      (rosette-typeo e r/@integer?)
      (rosette-asserto `(,r/@< ,b 2))
      (rosette-asserto `(,r/@> ,b 0))
      (rosette-asserto `(,r/@= ,e 1))

      (== a d)

      (== q `((,a ,b ,c) (,d ,e ,f)))
      ))
  '((((_.0 1 _.1) (_.0 1 _.2)) (=/= ((_.1 _.2))))))

;; Some normal tests for `=/=`
(test ""
  (run 1 (q)
    (fresh (x)
      (=/= x 0)
      (== q x)
      ))
  '((_.0 (=/= ((_.0 0))))))

(test ""
  (run 1 (q)
    (fresh (x)
      (=/= x 0)
      (== q x)
      ))
  '((_.0 (=/= ((_.0 0))))))

(test ""
  (run 1 (q)
    (fresh (x)
      (=/= x 0)
      (== x q)
      ))
  '((_.0 (=/= ((_.0 0))))))


(test ""
  (run 1 (q)
    (fresh (x a b)
      (=/= a b)
      (== a `(,x 111 222))
      (== b `(0 111 222))
      (== q x)
      ))
  '((_.0 (=/= ((_.0 0))))))

(test ""
  (run 1 (q)
    (fresh (x a b)
      (=/= a b)
      (== a `(,x 111 222))
      (== b `(0 111 222))
      (== x q)
      ))
  '((_.0 (=/= ((_.0 0))))))


;; An example of SMT type propagation
(test "==-and-smt: type propagration"
  (run 1 (q)
    (fresh (a b)
      (rosette-typeo a r/@integer?)
      (rosette-asserto `(,r/@= ,a 5))

      (== a b)
      (== q `(,a ,b))))
  '((5 5)))


(test "rosette-typeo-0"
  (run 3 (q)
    (rosette-typeo q r/@integer?))
  '(0 2 3))

;; ex1
(test "rosette-typeo-1"
  (run 3 (q)
    (fresh (a b)
      (rosette-typeo a r/@integer?)
      (== a #f)
      ))
  '())

(test "rosette-typeo-2"
  (run 3 (q)
    (fresh (a b)
      (rosette-typeo a r/@integer?)
      (rosette-typeo b r/@boolean?)
      (== a b)
      ))
  '())

(test "rosette-typeo-3"
  (run 3 (q)
    (fresh (a b)
      (rosette-typeo a r/@integer?)
      (rosette-typeo b r/@boolean?)
      (== a b)
      ))
  '())

(test "rosette-typeo-4"
  (run 3 (q)
    (fresh (a b) 
      (rosette-typeo b r/@integer?)
      (== a b)
      ))
  '(_.0 _.0 _.0))

(test "rosette-typeo-5"
  (run 3 (q)
    (fresh (a b)
      (rosette-typeo b r/@boolean?)
      (== a b)
      (rosette-typeo a r/@integer?)
      ))
  '())

(test "rosette-typeo-6"
  (run 3 (q)
    (fresh (a b)
      (rosette-typeo b r/@boolean?)
      (== a b)
      (== a 1)
      ))
  '())

;; ex2
(test "rosette-typeo-7"
  (run 3 (q)
    (fresh (a)
      (rosette-typeo a r/@integer?)
      (symbolo a)))
  '())

(test "rosette-typeo-8"
  (run 3 (q)
    (fresh (a)
      (symbolo a)
      (rosette-typeo a r/@integer?)
      ))
  '())

(test "rosette-typeo-9"
  (run 3 (q)
    (fresh (a)
      (numbero a)
      (rosette-typeo a r/@integer?)
      ))
  '(_.0 _.0 _.0))

(test "rosette-typeo-10"
  (run 3 (q)
    (fresh (a)
      (rosette-typeo a r/@integer?)
      (numbero a)
      ))
  '(_.0 _.0 _.0))
;; test fail

(test "rosette-typeo-11"
  (run 3 (q)
    (fresh (a)
      (rosette-typeo a r/@integer?)
      (rosette-typeo a r/@real?)
      ))
  '())

(test "rosette-typeo-12"
  (run 3 (q)
    (fresh (a)
      (numbero a)
      (rosette-typeo a r/@integer?)
      (rosette-typeo a r/@real?)
      ))
  '())

;; conde
(test "conde-1"
  (run 3 (q)
    (conde
      ((rosette-typeo q r/@integer?)
       (rosette-asserto `(,r/@equal? ,q 1)))
      ((rosette-typeo q r/@boolean?)
       (rosette-asserto `(,r/@equal? ,q #t)))
      ))
  '(1 #t))


(test "conde-2"
  (run 3 (q)
    (conde
      ((rosette-typeo q r/@integer?)
       (rosette-asserto `(,r/@equal? ,q 1)))
      ((rosette-typeo q r/@real?)
       (rosette-asserto `(,r/@equal? ,q 2.0)))
      ))
  '(1 2.0))

(test "inexact-integer?"
  (run 3 (q)
    (rosette-typeo q r/@real?)
    (rosette-asserto `(,r/@equal? ,q 2.0)))
  '(2.0))

(test "=/=-promotion-1"
  (run 1 (q)
    (fresh (x y)
      (rosette-typeo x r/@integer?)
      (=/= x 1)
      (=/= x 2)
      ))
  '(_.0))

(test "=/=-promotion-2"
  (run 1 (q)
    (fresh (x y)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@boolean?)
      (=/= x y)))
  '(_.0))
