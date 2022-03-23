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
(require (prefix-in r/ "../../rosette/rosette/base/core/function.rkt"))

(require "../../rosette/rosette/query/core.rkt") ; current-solver
;; (require "../../rosette/rosette/query/finitize.rkt")

(require "../logging.rkt")
(require "../test-check.rkt")
(require "../mk.rkt")
(require "../full-interp-extended.rkt")

;; (current-bitwidth 8)
;; (output-smt #t)
(current-solver
 (z3
  #:path "C:/env/z3/z3-4.8.7/z3-4.8.7-x64-win/bin/z3.exe"
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

;; (run 1 (q)
;;   (rosette-typeo q (r/~> r/@boolean? r/@boolean?))
;;   (rosette-asserto `(,r/@equal? (,q #t) #f)))

(let* ((qs (run 1 (q)
               (fresh (f)
                 (rosette-typeo f (r/~> r/@boolean? r/@boolean?))
                 (rosette-asserto `(,r/@equal? (,f #t) #f))
                 (== q f))))
       (f (car qs)))
  (list (f #t) (f #f)))

