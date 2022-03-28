#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")
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

(test "1"
  (run* (q)
    (fresh (s b- b0 b+)
      (s/declare-bito b-)
      (s/declare-bito b0)
      (s/declare-bito b+)
      (s/declareo s)
      (s/has-nego  s b-)
      (s/has-zeroo s b0)
      (s/has-poso  s b+)
      (== q (list s b+ b0 b-))))
  ;; TODO: I think this would be faster
  ;;       if has-...o used conde?
  (list
   (list (r/bv #b110 3) #t #t #f)
   (list (r/bv #b111 3) #t #t #t)
   (list (r/bv #b010 3) #f #t #f)
   (list (r/bv #b011 3) #f #t #t)
   (list (r/bv #b000 3) #f #f #f)
   (list (r/bv #b001 3) #f #f #t)
   (list (r/bv #b100 3) #t #f #f)
   (list (r/bv #b101 3) #t #f #t)))

(test "2"
  (run* (s)
    (s/declareo s)
    (s/uniono (r/bv #b110 3) (r/bv #b011 3) s))
  (list (r/bv #b111 3)))

(test "3"
  (run* (q)
    (s/declareo q)
    (s/membero (r/bv #b110 3) q))
  (list (r/bv #b010 3) (r/bv #b100 3)))

(test "4"
  (run* (s)
    (fresh (n)
      (s/declareo s)
      (s/alphao 5 s)))
  (list (r/bv #b100 3)))

(test "4z3"
  (run* (s)
    (fresh (n)
      (s/declareo s)
      (s/z3-alphao 5 s)))
  (list (r/bv #b100 3)))

(test "5"
  (run* (s)
    (fresh (s1 s2)
      (s/declareo s)
      (s/declareo s1)
      (s/declareo s2)
      (s/alphao -5 s1)
      (s/alphao 5 s2)
      (s/plus-alphao s1 s2 s)))
  (list (r/bv #b111 3)))

(test "6"
  (run* (s)
    (fresh (s1 s2)
      (s/declareo s)
      (s/declareo s1)
      (s/declareo s2)
      (s/alphao -5 s1)
      (s/alphao 5 s2)
      (s/pluso s1 s2 s)))
  (list (r/bv #b111 3) (r/bv #b111 3))) ;; TODO: why twice?

(test "7"
  (run* (s)
    (fresh (s1 s2)
      (s/declareo s)
      (s/declareo s1)
      (s/declareo s2)
      (s/alphao -5 s1)
      (s/alphao 5 s2)
      (s/plus-tableo s1 s2 s)))
  (list (r/bv #b111 3)))

(test "7z3"
  (run* (s)
    (fresh (s1 s2)
      (s/declareo s)
      (s/declareo s1)
      (s/declareo s2)
      (s/z3-alphao -5 s1)
      (s/z3-alphao 5 s2)
      (s/z3-plus-tableo s1 s2 s)))
  (list (r/bv #b111 3)))

(test "8"
  (run* (s)
    (fresh (s1 s2)
      (s/declareo s)
      (s/declareo s1)
      (s/declareo s2)
      (s/alphao -5 s1)
      (s/alphao 5 s2)
      (s/times-tableo s1 s2 s)))
  (list (r/bv #b001 3)))

(test "8"
  (run* (s)
    (fresh (s1 s2)
      (s/declareo s)
      (s/declareo s1)
      (s/declareo s2)
      (s/z3-alphao -5 s1)
      (s/z3-alphao 5 s2)
      (s/z3-times-tableo s1 s2 s)))
  (list (r/bv #b001 3)))

(test "9"
  (run* (s)
    (s/declareo s)
    (s/chas-nego  s)
    (s/chas-zeroo s)
    (s/chasnt-poso  s))
  (list (r/bv #b011 3)))

(test "10"
  (run* (s)
    (s/declareo s)
    (s/has-nego  s #t)
    (s/has-zeroo s #t)
    (s/has-poso  s #f))
  (list (r/bv #b011 3)))

;; TODO: check correctness
(test "11"
  (run* (s)
    (fresh (s1 s2 s3)
      (== (list s1 s2 s3) s)
      (s/declareo s1)
      (s/declareo s2)
      (s/declareo s3)
      (s/z3-plus-tableo s1 s2 s3)))
  '((bitvec-000 bitvec-000 bitvec-000)
    (bitvec-101 bitvec-001 bitvec-111)
    (bitvec-010 bitvec-001 bitvec-001)
    (bitvec-001 bitvec-010 bitvec-001)
    (bitvec-011 bitvec-011 bitvec-011)
    (bitvec-001 bitvec-011 bitvec-001)
    (bitvec-011 bitvec-010 bitvec-011)
    (bitvec-011 bitvec-001 bitvec-001)
    (bitvec-001 bitvec-001 bitvec-001)
    (bitvec-010 bitvec-011 bitvec-011)
    (bitvec-000 bitvec-100 bitvec-000)
    (bitvec-000 bitvec-110 bitvec-000)
    (bitvec-000 bitvec-101 bitvec-000)
    (bitvec-000 bitvec-111 bitvec-000)
    (bitvec-111 bitvec-000 bitvec-000)
    (bitvec-101 bitvec-000 bitvec-000)
    (bitvec-110 bitvec-000 bitvec-000)
    (bitvec-100 bitvec-000 bitvec-000)
    (bitvec-011 bitvec-000 bitvec-000)
    (bitvec-010 bitvec-010 bitvec-010)
    (bitvec-000 bitvec-010 bitvec-000)
    (bitvec-001 bitvec-000 bitvec-000)
    (bitvec-010 bitvec-000 bitvec-000)
    (bitvec-000 bitvec-011 bitvec-000)
    (bitvec-000 bitvec-001 bitvec-000)
    (bitvec-111 bitvec-111 bitvec-111)
    (bitvec-101 bitvec-111 bitvec-111)
    (bitvec-110 bitvec-111 bitvec-111)
    (bitvec-100 bitvec-111 bitvec-111)
    (bitvec-111 bitvec-110 bitvec-111)
    (bitvec-110 bitvec-110 bitvec-110)
    (bitvec-101 bitvec-110 bitvec-111)
    (bitvec-100 bitvec-110 bitvec-100)
    (bitvec-011 bitvec-111 bitvec-111)
    (bitvec-011 bitvec-110 bitvec-111)
    (bitvec-001 bitvec-111 bitvec-111)
    (bitvec-001 bitvec-110 bitvec-111)
    (bitvec-010 bitvec-111 bitvec-111)
    (bitvec-010 bitvec-110 bitvec-110)
    (bitvec-111 bitvec-101 bitvec-111)
    (bitvec-011 bitvec-101 bitvec-111)
    (bitvec-010 bitvec-101 bitvec-101)
    (bitvec-110 bitvec-101 bitvec-111)
    (bitvec-101 bitvec-101 bitvec-111)
    (bitvec-100 bitvec-101 bitvec-111)
    (bitvec-001 bitvec-101 bitvec-111)
    (bitvec-100 bitvec-100 bitvec-100)
    (bitvec-010 bitvec-100 bitvec-100)
    (bitvec-111 bitvec-100 bitvec-111)
    (bitvec-110 bitvec-100 bitvec-100)
    (bitvec-011 bitvec-100 bitvec-111)
    (bitvec-101 bitvec-100 bitvec-111)
    (bitvec-001 bitvec-100 bitvec-111)
    (bitvec-111 bitvec-011 bitvec-111)
    (bitvec-110 bitvec-011 bitvec-111)
    (bitvec-100 bitvec-011 bitvec-111)
    (bitvec-110 bitvec-010 bitvec-110)
    (bitvec-100 bitvec-010 bitvec-100)
    (bitvec-110 bitvec-001 bitvec-111)
    (bitvec-100 bitvec-001 bitvec-111)
    (bitvec-111 bitvec-010 bitvec-111)
    (bitvec-111 bitvec-001 bitvec-111)
    (bitvec-101 bitvec-010 bitvec-101)
    (bitvec-101 bitvec-011 bitvec-111)))

;; TODO: check correctness
(test "12"
  (run* (s)
    (fresh (s1 s2 s3)
      (== (list s1 s2 s3) s)
      (s/declareo s1)
      (s/declareo s2)
      (s/declareo s3)
      (s/z3-times-tableo s1 s2 s3)))
  '((bitvec-000 bitvec-000 bitvec-000)
    (bitvec-101 bitvec-001 bitvec-101)
    (bitvec-010 bitvec-010 bitvec-010)
    (bitvec-101 bitvec-101 bitvec-101)
    (bitvec-101 bitvec-110 bitvec-111)
    (bitvec-101 bitvec-100 bitvec-101)
    (bitvec-100 bitvec-100 bitvec-100)
    (bitvec-111 bitvec-110 bitvec-111)
    (bitvec-110 bitvec-110 bitvec-110)
    (bitvec-100 bitvec-110 bitvec-110)
    (bitvec-111 bitvec-100 bitvec-111)
    (bitvec-110 bitvec-100 bitvec-110)
    (bitvec-011 bitvec-100 bitvec-011)
    (bitvec-001 bitvec-100 bitvec-001)
    (bitvec-011 bitvec-110 bitvec-011)
    (bitvec-001 bitvec-110 bitvec-011)
    (bitvec-000 bitvec-100 bitvec-000)
    (bitvec-010 bitvec-110 bitvec-010)
    (bitvec-010 bitvec-100 bitvec-010)
    (bitvec-000 bitvec-110 bitvec-000)
    (bitvec-000 bitvec-101 bitvec-000)
    (bitvec-111 bitvec-111 bitvec-111)
    (bitvec-011 bitvec-111 bitvec-111)
    (bitvec-110 bitvec-111 bitvec-111)
    (bitvec-010 bitvec-111 bitvec-010)
    (bitvec-000 bitvec-111 bitvec-000)
    (bitvec-101 bitvec-111 bitvec-111)
    (bitvec-001 bitvec-111 bitvec-111)
    (bitvec-100 bitvec-111 bitvec-111)
    (bitvec-111 bitvec-101 bitvec-111)
    (bitvec-110 bitvec-101 bitvec-111)
    (bitvec-100 bitvec-101 bitvec-101)
    (bitvec-011 bitvec-101 bitvec-111)
    (bitvec-001 bitvec-101 bitvec-101)
    (bitvec-010 bitvec-101 bitvec-010)
    (bitvec-000 bitvec-010 bitvec-000)
    (bitvec-111 bitvec-010 bitvec-010)
    (bitvec-111 bitvec-011 bitvec-111)
    (bitvec-111 bitvec-000 bitvec-000)
    (bitvec-111 bitvec-001 bitvec-111)
    (bitvec-011 bitvec-010 bitvec-010)
    (bitvec-011 bitvec-011 bitvec-110)
    (bitvec-011 bitvec-000 bitvec-000)
    (bitvec-011 bitvec-001 bitvec-110)
    (bitvec-010 bitvec-000 bitvec-000)
    (bitvec-110 bitvec-001 bitvec-011)
    (bitvec-110 bitvec-000 bitvec-000)
    (bitvec-110 bitvec-011 bitvec-011)
    (bitvec-110 bitvec-010 bitvec-010)
    (bitvec-010 bitvec-001 bitvec-010)
    (bitvec-010 bitvec-011 bitvec-010)
    (bitvec-000 bitvec-001 bitvec-000)
    (bitvec-000 bitvec-011 bitvec-000)
    (bitvec-100 bitvec-000 bitvec-000)
    (bitvec-101 bitvec-011 bitvec-111)
    (bitvec-101 bitvec-010 bitvec-010)
    (bitvec-101 bitvec-000 bitvec-000)
    (bitvec-001 bitvec-011 bitvec-110)
    (bitvec-001 bitvec-001 bitvec-100)
    (bitvec-001 bitvec-010 bitvec-010)
    (bitvec-001 bitvec-000 bitvec-000)
    (bitvec-100 bitvec-010 bitvec-010)
    (bitvec-100 bitvec-001 bitvec-001)
    (bitvec-100 bitvec-011 bitvec-011)))

(test "sub1-table"
  (run* (s)
    (fresh (s1 s2)
      (== (list s1 s2) s)
      (s/declareo s1)
      (s/declareo s2)
      (s/z3-sub1-tableo s1 s2)))
  (list
   (list (r/bv #b000 3) (r/bv #b000 3))
   (list (r/bv #b011 3) (r/bv #b011 3))
   (list (r/bv #b101 3) (r/bv #b111 3))
   (list (r/bv #b001 3) (r/bv #b001 3))
   (list (r/bv #b100 3) (r/bv #b110 3))
   (list (r/bv #b010 3) (r/bv #b010 3))
   (list (r/bv #b110 3) (r/bv #b110 3))
   (list (r/bv #b111 3) (r/bv #b111 3))))

;; TODO: check correctness
(test "13"
  (run 20 (q)
    (fresh (n s)
      (== (list n s) q)
      (rosette-typeo n r/@integer?)
      (s/declareo s)
      (s/z3-alphao n s)))
  '((0 bitvec-010)
    (-1 bitvec-001)
    (1 bitvec-100)
    (2 bitvec-100)
    (-2 bitvec-001)
    (3 bitvec-100)
    (4 bitvec-100)
    (5 bitvec-100)
    (-3 bitvec-001)
    (6 bitvec-100)
    (7 bitvec-100)
    (8 bitvec-100)
    (9 bitvec-100)
    (-4 bitvec-001)
    (10 bitvec-100)
    (11 bitvec-100)
    (12 bitvec-100)
    (13 bitvec-100)
    (14 bitvec-100)
    (15 bitvec-100)))

(test "14-non-declarative-a"
  (run 1 (q)
    (fresh (n s)
      (== (list n s) q)
      (rosette-typeo n r/@integer?)
      (s/declareo s)
      (s/z3-alphao n s)))
  (list (list 0 (r/bv #b010 3))))