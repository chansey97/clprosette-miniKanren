#lang racket
(printf "synthesis.rkt\n")

;; NOTE: The original tests used cvc4 (I don't know why?). I used z3 instead.
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
(require "../test-check.rkt")

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

;; following https://barghouthi.github.io/2017/04/24/synthesis-primer/

(define (synthesize q exs)
  (fresh (a b)
    (let ()
      (fresh ()
        (rosette-typeo a r/@integer?)
        (rosette-typeo b r/@integer?)
        (let ()
          (define-symbolic* rx r/@integer?)
          (define-symbolic* ry r/@integer?)
          (let ((shape `(,r/@+ (,r/@* ,a ,rx) ,b)))
            (rosette-asserto `(,r/@forall (,rx ,ry)
                                          (,r/@=> (,r/@|| ,@(map (lambda (ex)
                                                                   `(,r/@&& (,r/@= ,rx ,(car ex))
                                                                            (,r/@= ,ry ,(cdr ex))))
                                                                 exs))
                                                  (,r/@= ,ry ,shape))))))
        r/purge
        (fresh (ax axb)
          (conde ((== a 1) (== ax 'x))
                 ((== a 0) (== ax 0))
                 ((=/= a 1) (=/= a 0) (== ax `(* ,a x))))
          (conde ((== ax 0) (== axb b))
                 ((=/= ax 0) (== b 0) (== axb ax))
                 ((=/= ax 0) (=/= b 0) (== axb `(+ ,ax ,b))))
          (== q `(lambda (x) ,axb)))))))


(test "syn-inc"
  (run* (q) (synthesize q '((1 . 2) (2 . 3))))
  '((lambda (x) (+ x 1))))

(test "syn-double"
  (run* (q) (synthesize q '((1 . 2) (2 . 4))))
  '((lambda (x) (* 2 x))))

(test "syn-const"
  (run* (q) (synthesize q '((1 . 2) (2 . 2))))
  '((lambda (x) 2)))

(test "syn-lin"
  (run* (q) (synthesize q '((1 . 3) (2 . 5))))
  '((lambda (x) (+ (* 2 x) 1))))

(test "syn-no"
  (run* (q) (synthesize q '((2 . 3) (3 . 2) (4 . 3))))
  '())
