#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
(provide (all-defined-out))

(define (lookupo x env val)
  (fresh (y v rest)
    (== `((,y . ,v) . ,rest) env)
    (conde
      [(== x y) (== v val)]
      [(=/= x y) (lookupo x rest val)])))

(define (evalo expr val)
  (eval-expro expr '() val))

(define (eval-expro expr env val)
  (conde
    [(fresh (x)
       (== `(var ,x) expr)
       (symbolo x)
       (lookupo x env val))]
    [(fresh (i)
       (== `(int ,i) expr)
       (== `(int ,i) val)
       (numbero i))]
    [(fresh (e1 e2 n1 n2 n3)
       (== `(plus ,e1 ,e2) expr)
       (numbero n1)
       (numbero n2)
       (numbero n3)
       (== `(int ,n3) val)
       (rosette-typeo n1 r/@integer?)
       (rosette-typeo n2 r/@integer?)
       (rosette-typeo n3 r/@integer?)
       (rosette-asserto `(,r/@= ,n3 (,r/@+ ,n1 ,n2)))
       (eval-expro e1 env `(int ,n1))
       (eval-expro e2 env `(int ,n2)))]
    [(fresh (e1 e2 n1 n2 n3)
       (== `(times ,e1 ,e2) expr)
       (numbero n1)
       (numbero n2)
       (numbero n3)
       (== `(int ,n3) val)
       (rosette-typeo n1 r/@integer?)
       (rosette-typeo n2 r/@integer?)
       (rosette-typeo n3 r/@integer?)
       (rosette-asserto `(,r/@= ,n3 (,r/@* ,n1 ,n2)))
       (eval-expro e1 env `(int ,n1))
       (eval-expro e2 env `(int ,n2)))]
    [(fresh (x y body)
       (== `(lam ,x ,y ,body) expr)
       (== `(clos ,x ,y ,body ,env) val)
       (symbolo x)
       (symbolo y))]
    [(fresh (e1 e2 x y body env^ arg)
       (== `(app ,e1 ,e2) expr)
       (eval-expro e1 env `(clos ,x ,y ,body ,env^))
       (symbolo x)
       (symbolo y)
       (eval-expro e2 env arg)
       ;; WEB is this right???
       (eval-expro body `((,y . ,arg) (,x . (clos ,x ,y ,body ,env^)) . ,env^) val))]
    [(fresh (e1 e2 e3 n)
       (== `(if0 ,e1 ,e2 ,e3) expr)
       (numbero n)
       (eval-expro e1 env `(int ,n))
       (rosette-typeo n r/@integer?)
       (conde
         [(rosette-asserto `(,r/@= ,n 0))
          (eval-expro e2 env val)]
         [(rosette-asserto `(,r/@! (,r/@= ,n 0)))
          (eval-expro e3 env val)]))]))
