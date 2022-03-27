#lang racket
(require "../../../rosette-bridge.rkt")
(require "../../../mk.rkt")
(require "../../../test-check.rkt")
(require "../../../logging.rkt")

;; (current-bitwidth 8)
;; (output-smt "./")
(current-solver
 (z3
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ;; ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

(test "real"
    (run 1 (q)
      (== q 2.0)
      (rosette-typeo q r/@real?)
      (rosette-asserto `(,r/@> ,q 0)))
  '(2.0))




