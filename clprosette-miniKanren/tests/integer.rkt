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
(output-smt "./")
(current-solver
 (z3
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

(test "real"
    (run 1 (q)
      (== q 2.0)
      (rosette-typeo q r/@real?)
      (rosette-asserto `(,r/@> ,q 0)))
  '(2.0))




