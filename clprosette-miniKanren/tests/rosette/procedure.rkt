#lang racket
(require "../../rosette-bridge.rkt")
(require "../../mk.rkt")
(require "../../test-check.rkt")
(require "../../logging.rkt")

;; (current-bitwidth 8)
;; (output-smt "./")
(current-solver
 (z3
  #:path "C:/env/z3/z3-4.8.7/z3-4.8.7-x64-win/bin/z3.exe"
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ;; ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

(let ()
  (define h (r/fv (r/~> r/@boolean? r/@boolean?)
                  (lambda (b)
                    (r/@if b #t #f))))
  (define (nevero)
    (conde
      [(== 1 2)]
      [(nevero)]))

  ;; '()
  ;; added disequality promotion for functions, but we really need it?
  ;; typically, users know a variable is a function, or users could check type first?
  ;; then use r/@exists to check... 
  (test "refute-procedure"
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
    '())
  )



