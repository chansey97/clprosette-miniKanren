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
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

;; Pair is an unsolvable type
;; As values of unsolvable types, symbolic pairs and lists cannot be created via define-symbolic[*].
;; https://docs.racket-lang.org/rosette-guide/sec_box.html

;; Note that unsolvable types doesn't mean that they cannot be synthesized,
;; but it cannot be synthesized with SMT, and exists some limitation.

;; IDEA:
;; In fact, all the assertion expression in `rosette-asserto`
;; can be written by helper functions by lifting logic variable to arguments!
(define (p-f b)
  (r/@if b (cons 1 2) (cons 4 #f))) ; (p-f b) is a symbolic pair.

(test "unsolvable type - box"
  (run 1 (q)
    (fresh (b)
      (rosette-typeo b r/@boolean?)
      (rosette-asserto `(,r/@boolean? (,r/@cdr (,p-f ,b))))
      (== q b)))
  '(#f))
;; But how to get the value of p or (p-f b)?

;; (run 1 (q)
;;     (fresh (b)
;;       (rosette-typeo b r/@boolean?)
;;       (rosette-asserto `(,r/@boolean? (,r/@cdr (,p-f ,b))))
;;       (== q b)))
;; TODO:
;; How to get the values of unsolvable types? how to get value of (,p-f ,b)?

;; An attempt:
(run 1 (q)
  (fresh (b p)
    (rosette-typeo b r/@boolean?)
    (lambda (st)
      (let ((p^ (r/reify-SM `(,p-f ,b) st)))
        (bind*
         st
         (lambda (st)
           (let* ((c (lookup-c p st))
                  (M (c-M c)))
             (set-c p (c-with-M c p^) st)))
         (rosette-asserto `(,r/@boolean? (,r/@cdr ,p^))))))
    (== q `(,b ,p))))
; term-type: contract violation
;   expected: term?
;   given: (cons (ite r-sym$1 1 4) (union [r-sym$1 2] [(! r-sym$1) #f]))

;; TODO: Truly support unsolvable type...

