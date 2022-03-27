#lang racket
(require "../../rosette/rosette/base/core/term.rkt")
(require "../../rosette/rosette/base/core/type.rkt")

(require "../../rosette/rosette/base/form/define.rkt")
(require (prefix-in r/ "../../rosette/rosette/base/form/control.rkt"))

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

;; (current-bitwidth 8)
;;(output-smt "./")
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

(define h (r/fv (r/~> r/@boolean? r/@boolean?)
                (lambda (b)
                  (r/@if b #t #f))))
(define (nevero)
  (conde
    [(== 1 2)]
    [(nevero)]))

(run 1 (q)
  (fresh (f g)
    (rosette-typeo f (r/~> r/@boolean? r/@boolean?))
    (rosette-typeo g (r/~> r/@boolean? r/@boolean?))

    (let ()
      (define-symbolic* rx r/@boolean?)
      (rosette-asserto `(,r/@forall (,rx) (,r/@equal? (,f ,rx) (,h ,rx))))) ; <-- here let's body can only have one goal 
    (let ()
      (define-symbolic* rx r/@boolean?)
      (rosette-asserto `(,r/@forall (,rx) (,r/@equal? (,g ,rx) (,h ,rx))))) ; <-- here let's body can only have one goal 
    (=/= f g)
    (nevero)
    ))
;; '()
;; added disequality promotion for functions, but we really need it?
;; typically, users know a variable is a function, or users could check type first?
;; then use r/@exists to check... 
