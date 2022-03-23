#lang racket
(require "../../rosette/rosette/base/core/term.rkt")
(require "../../rosette/rosette/base/core/type.rkt")
(require "../../rosette/rosette/base/form/define.rkt")

(require "../../rosette/rosette/solver/solver.rkt")
(require "../../rosette/rosette/solver/solution.rkt")
(require "../../rosette/rosette/solver/smt/z3.rkt")
(require (only-in "../../rosette/rosette/solver/smt/server.rkt" output-smt))

(require (prefix-in r/ "../../rosette/rosette/base/core/equality.rkt"))
(require (prefix-in r/ "../../rosette/rosette/base/core/bool.rkt"))
(require (prefix-in r/ "../../rosette/rosette/base/core/real.rkt"))

(require "../../rosette/rosette/query/core.rkt") ; current-solver
;; (require "../../rosette/rosette/query/finitize.rkt")

(require "../logging.rkt")
(require "../test-check.rkt")
(require "../mk.rkt")

;; (current-bitwidth 8)
;; (output-smt #t)
(current-solver
 (z3
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))

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
      (rosette-typeo val r/@integer?)
      
      (conde
        [(numbero expr)
         (rosette-typeo expr r/@integer?)
         ;; Originally used (== expr val).
         ;; Which version is preferable?
         ;; What are the tradeoffs?
         (rosette-asserto `(,r/@= ,expr ,val))
         (remove-one-elemento expr num* num*^)]

        [(fresh (a1 a2 n1 n2 num*^^)
           (rosette-typeo n1 r/@integer?)
           (rosette-typeo n2 r/@integer?)
           (== `(+ ,a1 ,a2) expr)
           (rosette-asserto `(,r/@= ,val (,r/@+ ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]

        [(fresh (a1 a2 n1 n2 num*^^)
           (rosette-typeo n1 r/@integer?)
           (rosette-typeo n2 r/@integer?)
           (== `(- ,a1 ,a2) expr)
           (rosette-asserto `(,r/@= ,val (,r/@- ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]

        [(fresh (a1 a2 n1 n2 num*^^)
           (rosette-typeo n1 r/@integer?)
           (rosette-typeo n2 r/@integer?)
           (== `(* ,a1 ,a2) expr)
           (rosette-asserto `(,r/@= ,val (,r/@* ,n1 ,n2)))
           (puzzleo a1 num* n1 num*^^)
           (puzzleo a2 num*^^ n2 num*^))]

        [(fresh (a1 a2 n1 n2 num*^^)
           (rosette-typeo n1 r/@integer?)
           (rosette-typeo n2 r/@integer?)
           (== `(/ ,a1 ,a2) expr)
           (rosette-asserto `(,r/@! (,r/@= ,n2 0)))
           (rosette-asserto `(,r/@= ,val (,r/@/ ,n1 ,n2)))
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
