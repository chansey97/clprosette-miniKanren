#lang racket/base
(provide (all-defined-out))

(define-syntax switch-log
  (syntax-rules ()
    [(_ printf/debug printf/info printf/warning #t)
     (begin
       (define (printf/debug x . xs) (apply printf (cons x xs)))
       (define (printf/info x . xs) (apply printf (cons x xs)))
       (define (printf/warning x . xs) (apply printf (cons x xs))))]
    [(_ printf/debug printf/info printf/warning #f)
     (begin
       (define (printf/debug x . xs) (void))
       (define (printf/info x . xs) (void))
       (define (printf/warning x . xs) (void)))]))

;; (switch-log printf/debug printf/info printf/warning #t)
(switch-log printf/debug printf/info printf/warning #f)
