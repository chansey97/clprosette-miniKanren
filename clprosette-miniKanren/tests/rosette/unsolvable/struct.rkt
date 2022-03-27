#lang racket
(require "../../../rosette-bridge.rkt")
(require "../../../mk.rkt")
(require "../../../test-check.rkt")
(require "../../../logging.rkt")

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

;; Like unsolvable built-in datatypes, symbolic structures cannot be created using define-symbolic.
;; Instead, they are created implicitly, by, for example, using an if expression together with a symbolic value.

(r/struct point (x y) #:transparent)

(test "struct #:transparent"
  (run 1 (q)
  (fresh (x y)
    (rosette-typeo x r/@integer?)
    (rosette-typeo y r/@integer?)
    (rosette-asserto `(,r/@equal? (,point 1 2) (,point ,x ,y)))
    (== q `(,x ,y))))
  '((1 2)))




