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
(require "../full-interp-extended.rkt")

;; (current-bitwidth 8)
;; (output-smt "./")
(current-solver
 (z3
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

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
(test "fib: synthesis value"
  (run 1 (q)
    (evalo `(letrec ((f
                      (lambda (n)
                        (if (< n 0) #f
                            (if (< n 2) n
                                (+ (f (- n 1)) (f (- n 2))))))))
              (f ',q))
           8))
  '(6))


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
