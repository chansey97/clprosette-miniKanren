#lang racket/base
(provide (all-defined-out))

(define (printf/debug x . xs) (void))
;; (define (printf/debug x . xs) (apply printf (cons x xs)))

(define (printf/info x . xs) (void))
;; (define (printf/info x . xs) (apply printf (cons x xs)))

;; (define (printf/warning x . xs) (void))
(define (printf/warning x . xs) (apply printf (cons x xs)))

