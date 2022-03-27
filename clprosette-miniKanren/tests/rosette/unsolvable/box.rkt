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

;; Box is an unsolvable type
;; As values of unsolvable types, symbolic pairs and lists cannot be created via define-symbolic[*].
;; https://docs.racket-lang.org/rosette-guide/sec_box.html

;; Note that unsolvable types doesn't mean that they cannot be synthesized,
;; but it cannot be synthesized with SMT, and exists some limitation.

;; IDEA:
;; In fact, all the assertion expression in `rosette-asserto`
;; can be written by helper functions by lifting logic variable to arguments!
(define (v2-f b v1)
  (r/@if b v1 (r/@box 3)))

(test "unsolvable type - box"
  (run 1 (q)
    (fresh (x b)
      (rosette-typeo x r/@integer?)
      (rosette-typeo b r/@boolean?)
      (let* ((v1 `(,r/@box ,x))
             ;; current mk's reify-to-rosette-symbols doesn't support thunk
             ;; use a helper function v2-f instead 
             ;; (v2 `(,r/@if ,b ,v1 (,r/@box 3)))
             ;; TODO: support r/@if, branch-and-merge, thunk in mk, but really needed?
             ) 
        (fresh ()
          (rosette-asserto `(,r/@= 4 (,r/@unbox (,v2-f ,b ,v1))))))
      (== q `(,x ,b))))
  '((4 #t)))


