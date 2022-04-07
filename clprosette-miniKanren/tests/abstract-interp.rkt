#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
(require "../logging.rkt")
(require "../test-check.rkt")
(require "sign-domain.rkt")

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

;;; abstract interpreter, inspired by the interpreter in:
;;;
;;; http://matt.might.net/articles/intro-static-analysis/


;;; Initial thoughts:

;;; 1. Having to declare a bitvector once and only once using 's/declareo' seems very error prone in complex queries/code.  At a minimum, having an error signalled, rather than failing silently, would be extremely friendly.  (See tests declaro-1 and declaro-2 to see the problem.)

;;; 2. s/declareo is non-relational, since declaraing the variable after use results in failure (once again, should really signal an error if possible, if not make fully relational).  (See declaro-3 and declaro-4.)

;;; 3. Not sure how to best mix sets/bitvectors with booleans, closures, etc., in the interpreter.  If we want an abstract evaluator that only handles sets, no problem.  If we want to also handle closures as values, for example, seems tricky, given the need to use 's/declareo' on sets.

;;; 4. The reified answer for (run* (q) (s/declareo q)) is just (_.0) -- no bit pattern in presented, no side-condition saying this is a set is included.  (See declaro-1 and declaro-3.)

;; What we would really like to do:
;; imagine a partially ground program
;; in the DSL being abstractly interpreted
;; you should be able to give abstract input/output pairs
;; and use that to synthesize the code
;; or
;; ake a ground program
;; and just run it backwards
;; give it a set of abstract values
;; and get back the input(s) that would produce that set of abstract values
;; that's the easier one
;; abstract angelic execution

;; should this code have any 's/declareo's?
(define alookupo
  (lambda (x aenv aval)
    (conde
      ((fresh (rest)
         (== `((,x . ,aval) . ,rest) aenv)))
      ((fresh (y av rest)
         (== `((,y . ,av) . ,rest) aenv)
         (symbolo y)
         (=/= y x)
         (alookupo x rest aval))))))



(define aevalo
  (lambda (expr aenv aval)
    (conde
      [(symbolo expr) (alookupo expr aenv aval)]
      
      [(numbero expr) (s/z3-alphao expr aval)]
      
      [(fresh (e1 e2 av1 av2)
         (== `(+ ,e1 ,e2) expr)
         (s/declareo av1)
         (s/declareo av2)
         ;; is this the ideal ordering?
         (s/z3-plus-tableo av1 av2 aval)
         (aevalo e1 aenv av1)
         (aevalo e2 aenv av2))]

      [(fresh (e1 e2 av1 av2)
         (== `(* ,e1 ,e2) expr)
         (s/declareo av1)
         (s/declareo av2)
         ;; is this the ideal ordering?
         (s/z3-times-tableo av1 av2 aval)
         (aevalo e1 aenv av1)
         (aevalo e2 aenv av2))]

      ;;; hmmm---seems like there is a problem here:
      ;;; if we want to make zero? and if work separately,
      ;;; aevalo may return a bit vector or a boolean.
      ;;; How would this work, given the need for s/declareo?
      [(fresh (e1 e2 e3 av1)
         (== `(ifzero ,e1 ,e2 ,e3) expr)
         (s/declareo av1)
         ;; is this the ideal ordering?
         (aevalo e1 aenv av1)
         (conde
           [(s/chas-zeroo av1)
            (aevalo e2 aenv aval)]
           [(conde
              [(s/chas-poso av1)]
              [(s/chas-nego av1)])
            (aevalo e3 aenv aval)]))]

      [(fresh (x e body av aenv^)
         (== `(let ((,x ,e)) ,body) expr)
         (symbolo x)
         (s/declareo av)
         (== `((,x . ,av) . ,aenv) aenv^)
         (aevalo e aenv av)
         (aevalo body aenv^ aval))]
      
      )))

;;; Hmmm--no bit pattern?
(test "declaro-1"
  (run* (q)
    (s/declareo q))
  '(_.0))

;;; Hmmm--this seems tricky!
;;; An error would be better
(test "declaro-2"
  (run* (q)
    (s/declareo q)
    (s/declareo q))
  '(_.0))

;;; Compare with declareo-1 -- now can see that we have bit patterns.
(test "declaro-3"
  (run* (q)
    (s/declareo q)
    (s/chas-poso q))
  (list (r/bv #b100 3)
        (r/bv #b111 3)
        (r/bv #b110 3)
        (r/bv #b101 3)))

;;; Non-declarative behavior
;;; compare with declareo-3 -- just swapped order of goals
;;; An error would be friendlier
(todo "declareo-4"
      (run* (q)
        (s/chas-poso q)
        (s/declareo q))
      '())


(test "alookupo-1"
  (run 3 (q)
    (fresh (x aenv aval)
      (s/declareo aval)
      (s/chas-poso aval)
      (symbolo x)
      (== (list x aenv aval) q)
      (alookupo x aenv aval)))
  (list
   (list (list '_.0 (cons (cons '_.0 (r/bv #b100 3)) '_.1) (r/bv #b100 3)) '(sym _.0))
   (list (list '_.0 (cons (cons '_.0 (r/bv #b111 3)) '_.1) (r/bv #b111 3)) '(sym _.0))
   (list (list '_.0 (cons (cons '_.0 (r/bv #b110 3)) '_.1) (r/bv #b110 3)) '(sym _.0))))

(test "alookupo-2"
  (run* (q)
    (fresh (x aenv aval av1 av2)
      (s/declareo av1)
      (s/chas-poso av1)
      (s/declareo av2)
      (s/chas-nego av2)
      (== `((x . ,av1) (y . ,av2)) aenv)
      (== (list aenv aval) q)
      (alookupo 'x aenv aval)))
  '((((x . bitvec-100) (y . bitvec-001)) bitvec-100)
    (((x . bitvec-111) (y . bitvec-111)) bitvec-111)
    (((x . bitvec-111) (y . bitvec-101)) bitvec-111)
    (((x . bitvec-111) (y . bitvec-001)) bitvec-111)
    (((x . bitvec-111) (y . bitvec-011)) bitvec-111)
    (((x . bitvec-110) (y . bitvec-101)) bitvec-110)
    (((x . bitvec-110) (y . bitvec-111)) bitvec-110)
    (((x . bitvec-110) (y . bitvec-001)) bitvec-110)
    (((x . bitvec-110) (y . bitvec-011)) bitvec-110)
    (((x . bitvec-101) (y . bitvec-111)) bitvec-101)
    (((x . bitvec-101) (y . bitvec-011)) bitvec-101)
    (((x . bitvec-100) (y . bitvec-011)) bitvec-100)
    (((x . bitvec-100) (y . bitvec-111)) bitvec-100)
    (((x . bitvec-101) (y . bitvec-101)) bitvec-101)
    (((x . bitvec-100) (y . bitvec-101)) bitvec-100)
    (((x . bitvec-101) (y . bitvec-001)) bitvec-101)))


(test "alookupo-3"
  (run* (q)
    (fresh (x aenv aval av1 av2)
      (s/declareo av1)
      (s/chas-poso av1)
      (s/declareo av2)
      (s/chas-nego av2)      
      (== `((x . ,av1) (y . ,av2)) aenv)
      (== (list aenv aval) q)
      (alookupo 'y aenv aval)))
  '((((x . bitvec-100) (y . bitvec-001)) bitvec-001)
    (((x . bitvec-111) (y . bitvec-111)) bitvec-111)
    (((x . bitvec-111) (y . bitvec-101)) bitvec-101)
    (((x . bitvec-111) (y . bitvec-001)) bitvec-001)
    (((x . bitvec-111) (y . bitvec-011)) bitvec-011)
    (((x . bitvec-110) (y . bitvec-101)) bitvec-101)
    (((x . bitvec-110) (y . bitvec-111)) bitvec-111)
    (((x . bitvec-110) (y . bitvec-001)) bitvec-001)
    (((x . bitvec-110) (y . bitvec-011)) bitvec-011)
    (((x . bitvec-101) (y . bitvec-111)) bitvec-111)
    (((x . bitvec-101) (y . bitvec-011)) bitvec-011)
    (((x . bitvec-100) (y . bitvec-011)) bitvec-011)
    (((x . bitvec-100) (y . bitvec-111)) bitvec-111)
    (((x . bitvec-101) (y . bitvec-101)) bitvec-101)
    (((x . bitvec-100) (y . bitvec-101)) bitvec-101)
    (((x . bitvec-101) (y . bitvec-001)) bitvec-001)))


(test "aevalo-0a"
  (run* (q)
    (fresh (expr aval)
      (s/declareo aval)
      (== '3 expr)
      (== (list expr aval) q)
      (aevalo expr '() aval)))
  (list (list 3 (r/bv #b100 3))))

(test "aevalo-0b"
  (run 10 (q)
    (fresh (expr aval)
      (s/declareo aval)
      (numbero expr)
      (== (list expr aval) q)
      (aevalo expr '() aval)))
  (list
   (list 0 (r/bv #b010 3))
   (list -1 (r/bv #b001 3))
   (list 1 (r/bv #b100 3))
   (list 2 (r/bv #b100 3))
   (list 3 (r/bv #b100 3))
   (list -2 (r/bv #b001 3))
   (list 4 (r/bv #b100 3))
   (list -3 (r/bv #b001 3))
   (list -4 (r/bv #b001 3))
   (list -5 (r/bv #b001 3))))

(test "aevalo-1"
  (run 10 (q)
    (fresh (expr aval)
      (s/declareo aval)
      (== (list expr aval) q)
      (aevalo expr '() aval)))
  (list
   (list 0 (r/bv #b010 3))
   (list -1 (r/bv #b001 3))
   (list 1 (r/bv #b100 3))
   (list 2 (r/bv #b100 3))
   (list 3 (r/bv #b100 3))
   (list -2 (r/bv #b001 3))
   (list 4 (r/bv #b100 3))
   (list -3 (r/bv #b001 3))
   (list -4 (r/bv #b001 3))
   (list -5 (r/bv #b001 3))))

(test "aevalo-2"
  (run 30 (q)
    (fresh (expr aval op e1 e2)
      (s/declareo aval)
      (== `(,op ,e1 ,e2) expr)
      (== (list expr aval) q)
      (aevalo expr '() aval)))
  (list
   (list '(+ 0 0) (r/bv #b010 3))
   (list '(+ -1 0) (r/bv #b001 3))
   (list '(+ 0 1) (r/bv #b100 3))
   (list '(+ -1 1) (r/bv #b111 3))
   (list '(+ 1 -1) (r/bv #b111 3))
   (list '(+ -1 2) (r/bv #b111 3))
   (list '(+ 2 -2) (r/bv #b111 3))
   (list '(+ 3 -2) (r/bv #b111 3))
   (list '(+ 3 -3) (r/bv #b111 3))
   (list '(+ 0 2) (r/bv #b100 3))
   (list '(+ -2 0) (r/bv #b001 3))
   (list '(+ 1 0) (r/bv #b100 3))
   (list '(+ 3 0) (r/bv #b100 3))
   (list '(+ 3 -4) (r/bv #b111 3))
   (list '(+ 0 -4) (r/bv #b001 3))
   (list '(+ 1 -2) (r/bv #b111 3))
   (list '(+ 0 -5) (r/bv #b001 3))
   (list '(+ -1 -5) (r/bv #b001 3))
   (list '(+ 0 -6) (r/bv #b001 3))
   (list '(+ 0 -7) (r/bv #b001 3))
   (list '(+ 1 -7) (r/bv #b111 3))
   (list '(+ 0 -8) (r/bv #b001 3))
   (list '(+ 0 -9) (r/bv #b001 3))
   (list '(+ 4 0) (r/bv #b100 3))
   (list '(+ -3 -6) (r/bv #b001 3))
   (list '(+ 1 1) (r/bv #b100 3))
   (list '(+ 2 1) (r/bv #b100 3))
   (list '(+ 3 3) (r/bv #b100 3))
   (list '(+ 2 3) (r/bv #b100 3))
   (list '(+ 3 4) (r/bv #b100 3))))

(test "aevalo-3"
  (run 10 (q)
    (fresh (expr aenv aval e)
      (s/declareo aval)
      (== `(let . ,e) expr)
      (== (list expr aenv aval) q)
      (aevalo expr aenv aval)))
  (list
   (list (list '(let ((_.0 0)) 0) '_.1 (r/bv #b010 3)) '(sym _.0))
   (list (list '(let ((_.0 0)) -1) '_.1 (r/bv #b001 3)) '(sym _.0))
   (list (list '(let ((_.0 0)) _.0) '_.1 (vbv #b010 3)) '(sym _.0))
   (list (list '(let ((_.0 -1)) 1) '_.1 (r/bv #b100 3)) '(sym _.0))
   (list (list '(let ((_.0 1)) -1) '_.1 (r/bv #b001 3)) '(sym _.0))
   (list (list '(let ((_.0 -1)) _.0) '_.1 (r/bv #b001 3)) '(sym _.0))
   (list (list '(let ((_.0 2)) -1) '_.1 (r/bv #b001 3)) '(sym _.0))
   (list (list '(let ((_.0 -2)) 2) '_.1 (r/bv #b100 3)) '(sym _.0))
   (list (list '(let ((_.0 1)) _.0) '_.1 (r/bv #b100 3)) '(sym _.0))
   (list (list '(let ((_.0 -2)) -2) '_.1 (r/bv #b001 3)) '(sym _.0))))

(test "aevalo-4"
  (run 10 (q)
    (fresh (expr aenv aval id e)
      (s/declareo aval)
      (== `(let ([,id ,e]) x) expr)
      (== (list expr aenv aval) q)
      (aevalo expr aenv aval)))
  (list
   (list '(let ((x 0)) x) '_.0 (r/bv #b010 3))
   (list '(let ((x -1)) x) '_.0 (r/bv #b001 3))
   (list '(let ((x 1)) x) '_.0 (r/bv #b100 3))
   (list '(let ((x 2)) x) '_.0 (r/bv #b100 3))
   (list '(let ((x 3)) x) '_.0 (r/bv #b100 3))
   (list '(let ((x -2)) x) '_.0 (r/bv #b001 3))
   (list '(let ((x 4)) x) '_.0 (r/bv #b100 3))
   (list '(let ((x -3)) x) '_.0 (r/bv #b001 3))
   (list '(let ((x -4)) x) '_.0 (r/bv #b001 3))
   (list '(let ((x -5)) x) '_.0 (r/bv #b001 3))))

(test "aevalo-5"
  (run 10 (q)
    (fresh (expr e1 e2 e3 aval)
      (s/declareo aval)
      (== `(ifzero ,e1 ,e2 ,e3) expr)
      (== (list expr aval) q)
      (aevalo expr '() aval)))
  (list
   (list '(ifzero 0 0 _.0) (r/bv #b010 3))
   (list '(ifzero 0 -1 _.0) (r/bv #b001 3))
   (list '(ifzero 0 -2 _.0) (r/bv #b001 3))
   (list '(ifzero 0 1 _.0) (r/bv #b100 3))
   (list '(ifzero 0 -3 _.0) (r/bv #b001 3))
   (list '(ifzero 0 -4 _.0) (r/bv #b001 3))
   (list '(ifzero 0 -5 _.0) (r/bv #b001 3))
   (list '(ifzero 0 -6 _.0) (r/bv #b001 3))
   (list '(ifzero 0 2 _.0) (r/bv #b100 3))
   (list '(ifzero 0 -7 _.0) (r/bv #b001 3))))

(test "aevalo-6"
  (run 10 (q)
    (fresh (expr e1 e2 e3 aval)
      (s/declareo aval)
      (== '5 e1)
      (== `(ifzero ,e1 ,e2 ,e3) expr)
      (== (list expr aval) q)
      (aevalo expr '() aval)))
  (list
   (list '(ifzero 5 _.0 0) (r/bv #b010 3))
   (list '(ifzero 5 _.0 -1) (r/bv #b001 3))
   (list '(ifzero 5 _.0 1) (r/bv #b100 3))
   (list '(ifzero 5 _.0 2) (r/bv #b100 3))
   (list '(ifzero 5 _.0 3) (r/bv #b100 3))
   (list '(ifzero 5 _.0 -2) (r/bv #b001 3))
   (list '(ifzero 5 _.0 4) (r/bv #b100 3))
   (list '(ifzero 5 _.0 -3) (r/bv #b001 3))
   (list '(ifzero 5 _.0 -4) (r/bv #b001 3))
   (list '(ifzero 5 _.0 -5) (r/bv #b001 3))))

(test "wish-1"
  (run 10 (expr)
    (aevalo expr '() vec-zero))
  '(0 (+ 0 0) (* 0 1) (* 0 -1) (* -1 0) (* -2 0) (* -3 0) (* 0 -2) (* 0 -3) (* -4 0)))

(test "wish-2"
  (run 10 (expr)
    (aevalo expr '() vec-pos))
  '(1 2 3 4 5 6 7 8 9 10))
