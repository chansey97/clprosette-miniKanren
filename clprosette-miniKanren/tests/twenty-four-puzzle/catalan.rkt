#lang racket
(provide (all-defined-out))

(define (fac n)
  (cond
    [(= 0 n) 1]
    [(= 0 1) 1]
    [else (* n (fac (- n 1)))]))

(define (combo n k)
  (/ (fac n)
     (* (fac k) (fac (- n k)))))

(define (catalan n)
  (/ (combo (* 2 n) n)
     (+ n 1)))

(define (num-of-exps n o)
  (* (fac n) (catalan (- n 1)) (expt o (- n 1))))

(module+ main

  (catalan 0)
  (catalan 1)
  (catalan 2)
  (catalan 3)
  (catalan 4)
  ;; 1
  ;; 1
  ;; 2
  ;; 5
  ;; 14


  (num-of-exps 4 1)
  (num-of-exps 4 2)
  (num-of-exps 4 3)
  (num-of-exps 4 4)
  ;; 120
  ;; 960
  ;; 3240
  ;; 7680
  )





