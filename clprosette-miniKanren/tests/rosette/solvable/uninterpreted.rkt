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

