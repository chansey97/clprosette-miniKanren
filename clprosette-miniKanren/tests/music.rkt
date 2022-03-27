#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
(require "../test-check.rkt")
(printf "music.rkt\n")

(define perfect-consonant '(0 5 7))
(define consonant '(0 3 4 5 7 8 9))
(define imperfect-consonant '(3 4 8 9))

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

(define harmony
  '((1 (3 6 2 4 5))
    (2 (5 7))
    (3 (6))
    (4 (5 7))
    (5 (1))
    (6 (2 4))
    (7 (1))))

(define (interval-ino ds note harmony)
  (fresh (d dr)
    (== (cons d dr) ds)
    (rosette-typeo note r/@integer?)
    (rosette-typeo harmony r/@integer?)
    (conde
      ((rosette-asserto `(,r/@= (,r/@- ,note ,harmony) ,d)))
      ((rosette-asserto `(,r/@! (,r/@= (,r/@- ,note ,harmony) ,d)))
       (interval-ino dr note harmony)))))

(define (ino xs x)
  (fresh (y ys)
    (== (cons y ys) xs)
    (rosette-typeo x r/@integer?)
    (rosette-typeo y r/@integer?)
    (conde
      ((rosette-asserto `(,r/@= ,x ,y)))
      ((rosette-asserto `(,r/@! (,r/@= ,x ,y)))
       (ino ys x)))))

(define (nexto harmony prev-harmony cur-harmony)
  (fresh (p hs cs)
    (== (cons `(,p ,cs) hs) harmony)
    (rosette-typeo p r/@integer?)
    (rosette-typeo prev-harmony r/@integer?)
    (conde
      ((rosette-asserto `(,r/@= ,p ,prev-harmony))
       (ino cs cur-harmony))
      ((rosette-asserto `(,r/@! (,r/@= ,p ,prev-harmony)))
       (nexto hs prev-harmony cur-harmony)))))

(define (zico measure phrase position prev-note cur-note prev-harmony cur-harmony)
  (fresh ()
    (nexto harmony prev-harmony cur-harmony)
    (rosette-typeo position r/@integer?)
    (rosette-typeo measure r/@integer?)
    (conde
      ((rosette-asserto `(,r/@= 0 (,r/@modulo ,position ,measure)))
       (== cur-harmony 1)
       (interval-ino perfect-consonant cur-note cur-harmony))
      ((rosette-asserto `(,r/@! (,r/@= 0 (,r/@modulo ,position ,measure))))
       (interval-ino imperfect-consonant cur-note cur-harmony)))))

(define (musico measure phrase position prev-note prev-harmony m)
  (fresh ()
    (rosette-typeo position r/@integer?)
    ;; The following two variables seems always ground?
    ;; So Nada use `(* measure phrase)` directly.
    (rosette-typeo measure r/@integer?)
    (rosette-typeo phrase r/@integer?)
    (conde
      ((rosette-asserto `(,r/@= ,position ,(* measure phrase)))
       (== m '()))
      ((rosette-asserto `(,r/@< ,position ,(* measure phrase)))
       (fresh (position+1 cur-note cur-harmony rest-m)
         (== m (cons (list cur-note cur-harmony) rest-m))
         (rosette-typeo position+1 r/@integer?)
         (rosette-asserto `(,r/@= ,position+1 (,r/@+ 1 ,position)))
         (zico measure phrase position prev-note cur-note prev-harmony cur-harmony)
         (musico measure phrase position+1 cur-note cur-harmony rest-m))))))

(test "1"
  (run 1 (m)
    (musico 1 1 0 5 5 m))
  '(((1 1))))

(test "5" ;; slow
  (run 1 (m)
    (musico 5 1 0 5 5 m))
  '(((1 1) (6 3) (9 6) (5 2) (8 5))))

(test "4-2" ;; very slow
  (run 1 (m)
    (musico 4 2 0 5 5 m))
  '(((1 1) (9 6) (5 2) (8 5) (1 1) (6 3) (9 6) (5 2))))
