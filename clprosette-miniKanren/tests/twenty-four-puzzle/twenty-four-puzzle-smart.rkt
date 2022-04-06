#lang racket
(require "../../mk.rkt")
(require "../../mk-streaming-interface.rkt")
(require "../../rosette-bridge.rkt")
(require "../../test-check.rkt")
(printf "twenty-four-puzzle-smart.rkt\n")

(current-solver
 (z3
  ;; #:path "C:/env/z3/z3-4.8.7/z3-4.8.7-x64-win/bin/z3.exe"
  #:options (hash ':smt.random_seed 1
                  ;; ':smt.random_seed 2
                  ;; ':smt.random_seed 3
                  ;; ':smt.arith.solver 1
                  ;; ':smt.arith.solver 2 ; default:2 in z3-4.8.7
                  ':smt.arith.solver 6 ; default:6 in z3-4.8.12
                  )))


;;; Classic 24 math puzzle, as described at:
;;;
;;; https://www.mathsisfun.com/puzzles/24-from-8-8-3-3-solution.html
;;;
;;; and
;;;
;;; http://www.4nums.com/game/difficulties/

;;; This version of code is restricted to integer values, which means solutions like
;;;
;;; 8/(3-(8/3))
;;; = 8/(1/3)
;;; = 24
;;;
;;; do *not* work!

#|
;;; Original defn of remove-one-elemento, using (== x a) rather than (rosette-asserto `(,r/@= ,x ,a)).
;;; Which version is preferable?
;;; What are the tradeoffs?

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
|#

;;; optimized version, more in the spirit of 24:
;;; assumes that 'ls' is a list of integers in
;;; *non-decreasing* order.
(define remove-one-elemento
  (lambda (x ls out)
    (fresh (a d)
      (== `(,a . ,d) ls)
      (numbero a)
      (rosette-typeo a r/@integer?)
      (rosette-typeo x r/@integer?)
      (conde
        ((rosette-asserto `(,r/@= ,a ,x))
         (== d out))
        ((rosette-asserto `(,r/@< ,a ,x))
         (fresh (res)
           (== `(,a . ,res) out)
           (remove-one-elemento x d res)))))))

(define (op->r/op op)
  (cond
    [(equal? op '+)  r/@+]
    [(equal? op '-)  r/@-]
    [(equal? op '*)  r/@*]
    [(equal? op '/)  r/@/]))

(define puzzleo
  (lambda (expr num* max-ops val num*^ max-ops^)
    (fresh ()
      (rosette-typeo val r/@integer?)
      (rosette-typeo max-ops r/@integer?)
      (rosette-typeo max-ops^ r/@integer?)
      
      (conde
        
        [(numbero expr)
         (rosette-typeo expr r/@integer?)
         ;; Originally used (== expr val).
         ;; Which version is preferable?
         ;; What are the tradeoffs?
         (rosette-asserto `(,r/@&& (,r/@= ,expr ,val) (,r/@= ,max-ops ,max-ops^)))
         (remove-one-elemento expr num* num*^)]

        [(fresh (op e1 e2 n1 n2 num*^^ max-ops-1 max-ops^^)
           (rosette-typeo n1 r/@integer?)
           (rosette-typeo n2 r/@integer?)
           (rosette-typeo max-ops-1 r/@integer?)
           (== `(,op ,e1 ,e2) expr)
           (conde
             [(conde
                [(== '+ op)]
                [(== '* op)])
              (project (op)
                (rosette-asserto `(,r/@&& (,r/@< 0 ,max-ops) (,r/@= (,r/@- ,max-ops 1) ,max-ops-1) (,r/@= ,val (,(op->r/op op) ,n1 ,n2)))))
              (conde
                ;; break symmetry for commutative operators
                [(numbero e1)
                 (numbero e2)
                 (rosette-typeo e1 r/@integer?)
                 (rosette-typeo e2 r/@integer?)
                 (rosette-asserto `(,r/@<= ,e1 ,e2))]
                [(numbero e1)
                 (rosette-typeo e1 r/@integer?)
                 (fresh (o2 a2 b2)
                   (== `(,o2 ,a2 ,b2) e2))]
                [(fresh (o1 a1 b1)
                   (== `(,o1 ,a1 ,b1) e1))
                 (fresh (o2 a2 b2)
                   (== `(,o2 ,a2 ,b2) e2))])]
             [(== '- op)
              (rosette-asserto `(,r/@&& (,r/@< 0 ,max-ops) (,r/@= (,r/@- ,max-ops 1) ,max-ops-1) (,r/@= ,val (,r/@- ,n1 ,n2))))]
             [(== '/ op)
              (rosette-asserto `(,r/@&& (,r/@< 0 ,max-ops) (,r/@= (,r/@- ,max-ops 1) ,max-ops-1) (,r/@! (,r/@= ,n2 0)) (,r/@= ,val (,r/@/ ,n1 ,n2))))])
           (puzzleo e1 num* max-ops-1 n1 num*^^ max-ops^^)
           (puzzleo e2 num*^^ max-ops^^ n2 num*^ max-ops^))]
        
        ))
    ))

(define puzzle-drivero
  (lambda (expr num*)
    (puzzleo expr num* 3 24 '() 0)))

(test "remove-one-elemento-a"
  (run* (q)
    (fresh (x out)
      (== (list x out) q)
      (remove-one-elemento x '(2 2 10 10) out)))
  '((2 (2 10 10))
    (10 (2 2 10))))



(test "24-puzzle-refute-a"
  (run* (e) (puzzleo e '() 0 24 '() 0))
  '())

(test "24-puzzle-refute-b"
  (run* (e) (puzzleo e '(0) 1 24 '() 0))
  '())

(test "24-puzzle-refute-c"
  (run* (e) (puzzleo e '(1) 1 24 '() 0))
  '())



(test "24-puzzle-a-check-answer-a"
  (run* (e) (== '(* 8 (+ 1 (+ 1 1))) e) (puzzle-drivero e '(1 1 1 8)))
  '((* 8 (+ 1 (+ 1 1)))))

(test "24-puzzle-a-check-answer-b"
  (run* (e) (== '(+ 8 (+ 1 (+ 1 1))) e) (puzzle-drivero e '(1 1 1 8)))
  '())

;; mock
(define z3-counter-check-sat 0)
(define z3-counter-get-model 0)

;; *** z3-counter-check-sat count: 28203
;; *** z3-counter-get-model count: 41
;; (time (test "24-puzzle-i" ...))
;;     214 collections
;;     20.592048386s elapsed cpu time, including 0.275569252s collecting
;;     718.830567000s elapsed real time, including 0.277166000s collecting
;;     1743521856 bytes allocated, including 1708956160 bytes reclaimed
(time
 (test "24-puzzle-i"
   (let ((c1 z3-counter-check-sat)
         (c2 z3-counter-get-model))
     (let ((ans (streaming-run* (e) (puzzle-drivero e '(4 6 7 7)))))
       (printf "*** z3-counter-check-sat count: ~s\n" (- z3-counter-check-sat c1))
       (printf "*** z3-counter-get-model count: ~s\n" (- z3-counter-get-model c2))
       ans))    
   '((- 7 (- 7 (* 4 6)))
     (+ 4 (+ 6 (+ 7 7)))
     (* 4 (- 6 (- 7 7)))
     (+ 4 (+ 7 (+ 6 7)))
     (* 4 (/ 6 (/ 7 7)))
     (+ 6 (+ 4 (+ 7 7)))
     (* 4 (- 7 (- 7 6)))
     (+ 6 (+ 7 (+ 4 7)))
     (* 4 (- 7 (/ 7 6)))
     (* 6 (- 4 (- 7 7)))
     (* 4 (+ 6 (- 7 7)))
     (* 4 (+ 7 (- 6 7)))
     (* 4 (- (+ 6 7) 7))
     (* 4 (* 6 (/ 7 7)))
     (* 6 (/ 4 (/ 7 7)))
     (* 4 (/ (* 6 7) 7))
     (+ 7 (+ 4 (+ 6 7)))
     (* 6 (- 7 (- 7 4)))
     (+ 7 (+ 6 (+ 4 7)))
     (+ 7 (+ 7 (+ 4 6)))
     (* 6 (+ 4 (- 7 7)))
     (+ 7 (- (* 4 6) 7))
     (* 6 (+ 7 (- 4 7)))
     (* 6 (- (+ 4 7) 7))
     (* 6 (* 4 (/ 7 7)))
     (* 6 (/ (* 4 7) 7))
     (- (* 4 6) (- 7 7))
     (/ (* 4 6) (/ 7 7))
     (+ (+ 4 6) (+ 7 7))
     (+ (+ 4 7) (+ 6 7))
     (/ (* 7 7) (- 6 4))
     (+ (- 7 7) (* 4 6))
     (- (+ 7 (* 4 6)) 7)
     (/ (* 4 (* 6 7)) 7)
     (* (* 4 6) (/ 7 7))
     (+ (+ 6 7) (+ 4 7))
     (+ (* 4 6) (- 7 7))
     (/ (* 6 (* 4 7)) 7)
     (* (/ 7 7) (* 4 6))
     (/ (* 7 (* 4 6)) 7)
     (+ (+ 7 7) (+ 4 6)))))

(time
 (test "24-puzzle-j"
   (streaming-run* (e) (puzzle-drivero e '(1 2 5 10)))
   '((- 5 (- 1 (* 2 10)))
     (+ 5 (- (* 2 10) 1))
     (+ (- 5 1) (* 2 10))
     (- (* 2 10) (- 1 5))
     (- (+ 5 (* 2 10)) 1)
     (- (* 5 (/ 10 2)) 1)
     (- (/ (* 5 10) 2) 1)
     (/ (- (* 5 10) 1) 2)
     (+ (* 2 10) (- 5 1)))))

(time
 (test "24-puzzle-k"
   (streaming-run* (e) (puzzle-drivero e '(3 7 8 9)))
   '((* 3 (- 7 (- 8 9)))
     (* 3 (- 8 (/ 7 9)))
     (* 3 (- 9 (- 8 7)))
     (* 3 (- 9 (/ 8 7)))
     (* 3 (/ 8 (/ 9 7)))
     (* 3 (+ 7 (- 9 8)))
     (* 3 (+ 7 (/ 9 8)))
     (* 3 (+ 8 (/ 7 9)))
     (* 3 (+ 9 (- 7 8)))
     (* 3 (- (+ 7 9) 8))
     (* 3 (* 8 (/ 9 7)))
     (* 8 (- 3 (/ 7 9)))
     (* 8 (/ 3 (/ 9 7)))
     (* 8 (+ 3 (/ 7 9)))
     (* 8 (* 3 (/ 9 7)))
     (* 8 (/ (* 3 9) 7))
     (- (* 3 8) (/ 7 9))
     (/ (* 3 8) (/ 9 7))
     (+ (/ 7 9) (* 3 8))
     (* (* 3 8) (/ 9 7))
     (+ (* 3 8) (/ 7 9))
     (* (/ 9 7) (* 3 8)))))

(time
 (test "24-puzzle-a-all-streaming"
   (streaming-run* (e) (puzzle-drivero e '(1 1 1 8)))
   '((* 8 (+ 1 (+ 1 1))))))

(time
 (test "24-puzzle-g-all-streaming"
   (streaming-run* (e) (puzzle-drivero e '(2 2 10 10)))
   '((+ 2 (+ 2 (+ 10 10)))
     (+ 2 (+ 10 (+ 2 10)))
     (+ 10 (+ 2 (+ 2 10)))
     (+ 10 (+ 10 (+ 2 2)))
     (+ 10 (+ 10 (* 2 2)))
     (+ (+ 2 2) (+ 10 10))
     (+ (+ 2 10) (+ 2 10))
     (+ (* 2 2) (+ 10 10))
     (+ (+ 10 10) (+ 2 2))
     (+ (+ 10 10) (* 2 2)))))

(time
 (test "24-puzzle-h-all-streaming"
   (streaming-run* (e) (puzzle-drivero e '(2 2 2 12)))
   '((- 2 (- 2 (* 2 12)))
     (* 2 (- 2 (- 2 12)))
     (* 2 (- 12 (- 2 2)))
     (* 2 (/ 12 (/ 2 2)))
     (+ 2 (- (* 2 12) 2))
     (* 2 (+ 2 (- 12 2)))
     (* 2 (- (+ 2 12) 2))
     (* 2 (* 2 (/ 12 2)))
     (* 12 (- 2 (- 2 2)))
     (* 2 (+ 12 (- 2 2)))
     (* 2 (* 12 (/ 2 2)))
     (* 2 (/ (* 2 12) 2))
     (* 12 (/ 2 (/ 2 2)))
     (* 12 (+ 2 (- 2 2)))
     (* 12 (- (+ 2 2) 2))
     (+ (- 2 2) (* 2 12))
     (* 12 (* 2 (/ 2 2)))
     (* 12 (- (* 2 2) 2))
     (* 12 (/ (+ 2 2) 2))
     (* 12 (/ (* 2 2) 2))
     (* (/ 2 2) (* 2 12))
     (- (* 2 12) (- 2 2))
     (/ (* 2 12) (/ 2 2))
     (* (+ 2 2) (/ 12 2))
     (- (+ 2 (* 2 12)) 2)
     (* (* 2 2) (/ 12 2))
     (/ (* 2 (* 2 12)) 2)
     (* (* 2 12) (/ 2 2))
     (+ (* 2 12) (- 2 2))
     (* (/ 12 2) (+ 2 2))
     (* (/ 12 2) (* 2 2))
     (/ (* 12 (+ 2 2)) 2)
     (/ (* 12 (* 2 2)) 2))))
