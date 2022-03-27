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

;; Vector is an unsolvable type
;; As values of unsolvable types, symbolic pairs and lists cannot be created via define-symbolic[*].
;; https://docs.racket-lang.org/rosette-guide/sec_vec.html

;; Note that unsolvable types doesn't mean that they cannot be synthesized,
;; but it cannot be synthesized with SMT, and exists some limitation.

(test "unsolvable type - vector"
  (run 1 (q)
    (fresh (x y z n)
      (rosette-typeo x r/@integer?)
      (rosette-typeo y r/@integer?)
      (rosette-typeo z r/@integer?)
      (rosette-typeo n r/@integer?)
      (let* ((xs `(,r/@take (,r/@list ,x ,y ,z) ,n))
             (vs `(,r/@list->vector ,xs)))
        (fresh ()
          (rosette-asserto `(,r/@< ,n 3))
          (rosette-asserto `(,r/@= 4 (,r/@vector-ref ,vs (,r/@sub1 ,n))))))
      (== q `(,x ,y ,z, n))))
  '((4 0 0 1)))

