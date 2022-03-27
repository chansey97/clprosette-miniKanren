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
(require (prefix-in r/ "../../rosette/rosette/base/core/bitvector.rkt"))

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
  #:path "C:/env/z3/z3-4.8.7/z3-4.8.7-x64-win/bin/z3.exe"
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

(test "bitwise version of deMorgan's law:"
  (run 1 (q)
    (fresh (x y)
      (rosette-typeo x (r/bitvector 64))
      (rosette-typeo y (r/bitvector 64))
      (rosette-asserto `(,r/!
                         (,r/@equal? (,r/@bvand (,r/@bvnot ,x) (,r/@bvnot ,y))
                                     (,r/@bvnot (,r/@bvor ,x ,y)))))
      ))
  '())

;; Signed comparison
(test "signed comparison"
  (run 1 (q)
    (fresh (a b)
      (rosette-typeo a (r/bitvector 4))
      (rosette-typeo b (r/bitvector 4))
      (rosette-asserto `(,r/!
                         (,r/@equal? (,r/@bvule ,a ,b)
                                     (,r/@bvsle ,a ,b))))
      (== q `(,a ,b)) ))
  (list (list (r/bv #x0 4) (r/bv #xe 4))))
