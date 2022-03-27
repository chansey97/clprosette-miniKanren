#lang racket
(require "../../../../rosette/rosette/base/core/term.rkt")
(require "../../../../rosette/rosette/base/core/type.rkt")

(require "../../../../rosette/rosette/base/form/define.rkt")

(require "../../../../rosette/rosette/solver/solver.rkt")
(require "../../../../rosette/rosette/solver/solution.rkt")
(require "../../../../rosette/rosette/solver/smt/z3.rkt")
(require (only-in "../../../../rosette/rosette/solver/smt/server.rkt" output-smt))

(require (prefix-in r/ "../../../../rosette/rosette/base/core/equality.rkt"))
(require (prefix-in r/ "../../../../rosette/rosette/base/core/bool.rkt"))
(require (prefix-in r/ "../../../../rosette/rosette/base/core/real.rkt"))
(require (prefix-in r/ "../../../../rosette/rosette/base/adt/list.rkt"))

(require "../../../../rosette/rosette/query/core.rkt") ; current-solver
;; (require "../../../../rosette/rosette/query/finitize.rkt")

(require "../../../logging.rkt")
(require "../../../test-check.rkt")
(require "../../../mk.rkt")

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

;; List is an unsolvable type
;; As values of unsolvable types, symbolic pairs and lists cannot be created via define-symbolic[*].
;; https://docs.racket-lang.org/rosette-guide/sec_pair.html

;; Note that unsolvable types doesn't mean that they cannot be synthesized,
;; but it cannot be synthesized with SMT, and exists some limitation.

(test "unsolvable type - list 1"
  (run 1 (q)
    (fresh (x y z n)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-typeo z r/@integer?)
      (rosette-typeo n r/@integer?)
      (rosette-asserto `(,r/@= (,r/@length (,r/@take (,r/@list ,x ,y ,z) ,n)) 2))
      (rosette-asserto `(,r/@! (,r/@equal? (,r/@take (,r/@list ,x ,y ,z) ,n) (,r/@reverse (,r/@take (,r/@list ,x ,y ,z) ,n)))))
      (rosette-asserto `(,r/@equal? (,r/@take (,r/@list ,x ,y ,z) ,n) (,r/@sort (,r/@take (,r/@list ,x ,y ,z) ,n) ,r/@<)))
      (== q `(,x ,y ,z, n))))
  '((1 2 2 2)))

(test "unsolvable type - list 2"
  (run 1 (q)
    (fresh (x y z n)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-typeo z r/@integer?)
      (rosette-typeo n r/@integer?)
      (let ((xs `(,r/@take (,r/@list ,x ,y ,z) ,n)))
        (fresh ()
          (rosette-asserto `(,r/@= (,r/@length ,xs) 2))
          (rosette-asserto `(,r/@! (,r/@equal? ,xs (,r/@reverse ,xs))))
          (rosette-asserto `(,r/@equal? ,xs (,r/@sort ,xs ,r/@<)))))
      (== q `(,x ,y ,z, n))))
  '((1 2 2 2)))

