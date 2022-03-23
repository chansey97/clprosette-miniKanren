#lang racket
(require "../mk.rkt")
(require "../test-check.rkt")

(define remove-one-elemento
  (lambda (x ls out)
    (fresh (a d)
      (== `(,a . ,d) ls)
      (conde
        ((== x a) (== d out))
        ((=/= x a)
         (fresh (res)
           (== `(,a . ,res) out)
           (remove-one-elemento x d res)))))))

(define puzzleo
  (lambda (expr num* val num*^)
    (fresh ()
      (smt-typeo val 'Int)
      
      (conde
        [(numbero expr)
         (smt-typeo expr 'Int)
         ;; Originally used (== expr val).
         ;; Which version is preferable?
         ;; What are the tradeoffs?
         (smt-asserto `(= ,expr ,val))
         (remove-one-elemento expr num* num*^)]

        [(fresh (a1 a2 n1 n2 num*^^)
           (smt-typeo n1 'Int)
           (smt-typeo n2 'Int)
           (== `(+ ,a1 ,a2) expr)
           (smt-asserto `(= ,val (+ ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]

        [(fresh (a1 a2 n1 n2 num*^^)
           (smt-typeo n1 'Int)
           (smt-typeo n2 'Int)
           (== `(- ,a1 ,a2) expr)
           (smt-asserto `(= ,val (- ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]

        [(fresh (a1 a2 n1 n2 num*^^)
           (smt-typeo n1 'Int)
           (smt-typeo n2 'Int)
           (== `(* ,a1 ,a2) expr)
           (smt-asserto `(= ,val (* ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]

        [(fresh (a1 a2 n1 n2 num*^^)
           (smt-typeo n1 'Int)
           (smt-typeo n2 'Int)
           (== `(/ ,a1 ,a2) expr)
           (smt-asserto `(not (= ,n2 0)))
           (smt-asserto `(= ,val (div ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]
        ))
    ))

(test "remove-one-elemento-a"
  (run* (q)
    (fresh (x out)
      (== (list x out) q)
      (remove-one-elemento x '(2 2 10 10) out)))
  '((2 (2 10 10))
    (10 (2 2 10))))

(test "24-puzzle-a"
  (run 1 (e) (puzzleo e '(1 1 1 8) 24 '()))
  '((* 8 (+ 1 (+ 1 1)))))
