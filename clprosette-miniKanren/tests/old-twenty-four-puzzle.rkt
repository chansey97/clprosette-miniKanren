#lang racket
(require "mk.rkt")
(require "test-check.rkt")
(printf "old-twenty-four-puzzle.rkt\n")

;;; Classic 24 math puzzle, as described at:
;;;
;;; https://www.mathsisfun.com/puzzles/24-from-8-8-3-3-solution.html

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
    (conde    
      
      [(numbero expr) (== expr val) (remove-one-elemento expr num* num*^)]

      [(fresh (a1 a2 n1 n2 num*^^)
         (smt-typeo val 'Int)
         (smt-typeo n1 'Int)
         (smt-typeo n2 'Int)
         (== `(+ ,a1 ,a2) expr)
         (smt-asserto `(= ,val (+ ,n1 ,n2)))
         (puzzleo a1 num* n1 num*^^)
         (puzzleo a2 num*^^ n2 num*^))]

      [(fresh (a1 a2 n1 n2 num*^^)
         (smt-typeo val 'Int)
         (smt-typeo n1 'Int)
         (smt-typeo n2 'Int)
         (== `(- ,a1 ,a2) expr)
         (smt-asserto `(= ,val (- ,n1 ,n2)))
         (puzzleo a1 num* n1 num*^^)
         (puzzleo a2 num*^^ n2 num*^))]

      [(fresh (a1 a2 n1 n2 num*^^)
         (smt-typeo val 'Int)
         (smt-typeo n1 'Int)
         (smt-typeo n2 'Int)
         (== `(* ,a1 ,a2) expr)
         (smt-asserto `(= ,val (* ,n1 ,n2)))
         (puzzleo a1 num* n1 num*^^)
         (puzzleo a2 num*^^ n2 num*^))]

      [(fresh (a1 a2 n1 n2 num*^^)
         (smt-typeo val 'Int)
         (smt-typeo n1 'Int)
         (smt-typeo n2 'Int)
         (== `(/ ,a1 ,a2) expr)
         (smt-asserto `(not (= ,n2 0)))
         (smt-asserto `(= ,val (div ,n1 ,n2)))
         (puzzleo a1 num* n1 num*^^)
         (puzzleo a2 num*^^ n2 num*^))]
      
      )))

(run 1 (q)
  (fresh (e nums out nums^)
    (== (list e nums out nums^) q)
    (== '(8 8 3 3) nums)
    (== '(* 3 8) e)
    (puzzleo e nums out nums^)))

(run 1 (q)
  (fresh (e nums out)
    (== (list e nums out) q)
    (== '(8 8 3 3) nums)
    (== '(/ 8 (- 3 (/ 8 3))) e)
    (puzzleo e nums out '())))

;; 8/(3-(8/3))
;; = 8/(1/3)
;; = 24
(test "24-puzzle-test-solution"
  (run 1 (e)
    (fresh (nums)
      (== '(8 8 3 3) nums)
      (== '(/ 8 (- 3 (/ 8 3))) e)
      (puzzleo e nums 24 '())))
  '?)

(test "24-puzzle-b"
  (run 1 (e)
    (fresh (nums)
      (== '(1 1 1 8) nums)
      (puzzleo e nums 24 '())))
  '((* 8 (+ 1 (+ 1 1)))))


;; #!eof

;; (test "24-puzzle-a"
;;       (run 1 (q)
;;            (fresh (e nums)
;;                   (== (list e nums) q)
;;                   (puzzleo e nums 24 '())))
;;       '?)

;; (test "24-puzzle-b"
;;       (run 10 (e)
;;            (fresh (nums n1 n2 n3 n4)
;;                   (== `(,n1, n2 ,n3 ,n4) nums)
;;                   (smt-typeo n1 'Int)
;;                   (smt-typeo n2 'Int)
;;                   (smt-typeo n3 'Int)
;;                   (smt-typeo n4 'Int)
;;                   (smt-asserto `(> ,n1 0))
;;                   (smt-asserto `(> ,n2 0))
;;                   (smt-asserto `(> ,n3 0))
;;                   (smt-asserto `(> ,n4 0))
;;                   (puzzleo e nums 24 '())))
;;       '?)

;; (test "24-puzzle-c"
;;       (run 1 (e)
;;            (fresh (nums n1 n2 n3 n4)
;;                   (== `(,n1, n2 ,n3 ,n4) nums)
;;                   (== n1 8)
;;                   (smt-typeo n2 'Int)
;;                   (smt-typeo n3 'Int)
;;                   (smt-typeo n4 'Int)
;;                   (smt-asserto `(> ,n1 0))
;;                   (smt-asserto `(> ,n2 0))
;;                   (smt-asserto `(> ,n3 0))
;;                   (smt-asserto `(> ,n4 0))
;;                   (puzzleo e nums 24 '())))
;;       '?)

;; (test "24-puzzle-d"
;;       (run 1 (e)
;;            (fresh (nums n1 n2 n3 n4)
;;                   (== `(,n1, n2 ,n3 ,n4) nums)
;;                   (== n1 8)
;;                   (== n2 8)
;;                   (smt-typeo n3 'Int)
;;                   (smt-typeo n4 'Int)
;;                   (smt-asserto `(> ,n1 0))
;;                   (smt-asserto `(> ,n2 0))
;;                   (smt-asserto `(> ,n3 0))
;;                   (smt-asserto `(> ,n4 0))
;;                   (puzzleo e nums 24 '())))
;;       '?)

;; (test "24-puzzle-e"
;;       (run 1 (e)
;;            (fresh (nums n1 n2 n3 n4)
;;                   (== `(,n1, n2 ,n3 ,n4) nums)
;;                   (== n1 8)
;;                   (== n2 8)
;;                   (== n3 3)
;;                   (smt-typeo n4 'Int)
;;                   (smt-asserto `(> ,n1 0))
;;                   (smt-asserto `(> ,n2 0))
;;                   (smt-asserto `(> ,n3 0))
;;                   (smt-asserto `(> ,n4 0))
;;                   (puzzleo e nums 24 '())))
;;       '?)

;; (test "24-puzzle-f"
;;       (run 1 (e)
;;            (fresh (nums n1 n2 n3 n4)
;;                   (== `(,n1, n2 ,n3 ,n4) nums)
;;                   (== n1 8)
;;                   (== n2 8)
;;                   (== n3 3)
;;                   (== n4 3)
;;                   (smt-asserto `(> ,n1 0))
;;                   (smt-asserto `(> ,n2 0))
;;                   (smt-asserto `(> ,n3 0))
;;                   (smt-asserto `(> ,n4 0))
;;                   (puzzleo e nums 24 '())))
;;       '?)

;; #!eof

;; (test "24-puzzle-a"
;;       (run 1 (q)
;;            (puzzleo q '(8 8 3 3) 24 '()))
;;       '?)


;; #!eof

;; (define Ao
;;   (lambda (expr num)
;;     (conde    

;;      [(numbero expr) (== expr num)]

;;      [(fresh (a1 a2 n1 n2)
;;              (== `(+ ,a1 ,a2) expr)
;;              (smt-typeo num 'Int)
;;              (smt-typeo n1 'Int)
;;              (smt-typeo n2 'Int)
;;              (smt-asserto `(= ,num (+ ,n1 ,n2)))
;;              (Ao a1 n1)
;;              (Ao a2 n2))]

;;      [(fresh (a1 a2 n1 n2)
;;              (== `(- ,a1 ,a2) expr)
;;              (smt-typeo num 'Int)
;;              (smt-typeo n1 'Int)
;;              (smt-typeo n2 'Int)
;;              (smt-asserto `(= ,num (- ,n1 ,n2)))
;;              (Ao a1 n1)
;;              (Ao a2 n2))]

;;      [(fresh (a1 a2 n1 n2)
;;              (== `(* ,a1 ,a2) expr)
;;              (smt-typeo num 'Int)
;;              (smt-typeo n1 'Int)
;;              (smt-typeo n2 'Int)
;;              (smt-asserto `(= ,num (* ,n1 ,n2)))
;;              (Ao a1 n1)
;;              (Ao a2 n2))]

;;      [(fresh (a1 a2 n1 n2)
;;              (== `(/ ,a1 ,a2) expr)
;;              (smt-typeo num 'Int)
;;              (smt-typeo n1 'Int)
;;              (smt-typeo n2 'Int)
;;              (smt-asserto `(not (= ,n2 0)))
;;              (smt-asserto `(= ,num (div ,n1 ,n2)))
;;              (Ao a1 n1)
;;              (Ao a2 n2))]

;;      )))

;; (test "24-a"
;;       (run 100 (q)
;;            (Ao q 24))
;;       '(24
;;         (+ 24 0) (+ 23 1) (+ 22 2) (+ 21 3) (+ 20 4) (+ 19 5)
;;         (+ 18 6) (+ 17 7) (+ 16 8) (- 24 0) (+ 15 9) (+ 14 10)
;;         (- 25 1) (+ 13 11) (+ 12 12) (- 26 2) (+ 11 13) (+ 10 14)
;;         (- 27 3) (+ 9 15) (+ 8 16) (- 28 4) (+ 7 17) (+ 6 18)
;;         (- 29 5) (+ 5 19) (+ 4 20) (- 30 6) (+ 3 21) (+ 2 22)
;;         (- 31 7) (+ 1 23) (+ 0 24) (- 32 8) (+ -1 25) (+ -2 26)
;;         (- 33 9) (+ -3 27) (+ -4 28) (- 34 10) (+ -5 29) (+ -6 30)
;;         (- 35 11) (+ -7 31) (+ -8 32) (- 36 12) (+ -9 33) (+ -10 34)
;;         (- 37 13) (+ -11 35) (+ -12 36) (- 38 14) (+ -13 37)
;;         (+ -14 38) (- 39 15) (+ -15 39) (+ 25 -1) (- 40 16)
;;         (+ 26 -2) (+ -16 40) (- 41 17) (+ 27 -3) (* 24 1) (+ 28 -4)
;;         (- 42 18) (+ 29 -5) (+ 30 -6) (- 43 19) (+ 31 -7) (* 1 24)
;;         (+ 32 -8) (- 44 20) (+ 33 -9) (+ 34 -10) (- 45 21)
;;         (+ 35 -11) (* -1 -24) (+ 36 -12) (- 46 22) (+ 37 -13)
;;         (+ 38 -14) (- 47 23) (+ 39 -15) (* -2 -12) (+ 40 -16)
;;         (- 48 24) (+ 41 -17) (/ -24 -1) (+ 42 -18) (- 49 25)
;;         (+ 43 -19) (* -3 -8) (+ 44 -20) (- 50 26) (+ 45 -21)
;;         (+ 46 -22) (- 51 27) (+ 47 -23) (* -4 -6) (+ 48 -24)
;;         (- 52 28) (+ 49 -25) (/ 24 1) (+ 50 -26) (- 53 29)
;;         (+ 51 -27) (* -24 -1) (+ 52 -28) (- 54 30) (+ 53 -29)
;;         (+ 54 -30) (- 55 31) (+ 55 -31) (* -12 -2) (+ 56 -32)
;;         (- 56 32) (+ 57 -33) (/ 48 2) (+ 58 -34) (- 57 33)
;;         (+ 59 -35) (* -8 -3) (+ 60 -36) (- 58 34) (+ 61 -37)
;;         (+ 62 -38) (- 59 35) (+ 63 -39) (* -6 -4) (+ 64 -40)
;;         (- 60 36) (+ 65 -41) (/ 49 2) (+ 66 -42) (- 61 37)
;;         (+ 67 -43) (* 2 12) (+ 68 -44) (- 62 38) (+ 69 -45)
;;         (+ 70 -46) (- 63 39) (+ 71 -47) (* 3 8) (+ 72 -48) (- 23 -1)
;;         (+ 73 -49) (/ 72 3) (+ 74 -50) (- 22 -2) (+ 75 -51) (* 4 6)
;;         (+ 76 -52) (- 64 40) (+ 77 -53) (+ 24 (+ 0 0)) (+ 78 -54)
;;         (- 21 -3) (+ -17 41) (* 6 4) (+ -18 42) (- 20 -4) (+ -19 43)
;;         (/ 73 3) (+ -20 44) (- 19 -5) (+ -21 45) (* 8 3) (+ -22 46)
;;         (- 18 -6) (+ -23 47) (+ -24 48) (- 17 -7) (+ -25 49)
;;         (* 12 2) (+ -26 50) (- 16 -8) (+ -27 51) (/ 74 3) (+ -28 52)
;;         (- 15 -9) (+ -29 53) (+ 23 (+ 2 -1)) (+ -30 54) (- 14 -10)
;;         (+ -31 55) (/ 96 4) (+ -32 56) (- 13 -11) (+ -33 57)
;;         (+ (+ 24 0) 0) (+ -34 58) (- 12 -12) (+ -35 59) (/ 97 4)
;;         (+ -36 60) (- 11 -13) (+ -37 61) (+ 27 (+ -1 -2)) (+ -38 62)
;;         (- 10 -14) (+ -39 63) (/ 98 4) (+ -40 64) (- 9 -15)
;;         (+ -41 65) (+ -42 66) (- 8 -16) (+ -43 67) (/ 99 4)
;;         (+ -44 68) (- 7 -17) (+ -45 69) (+ 26 (+ -1 -1)) (+ -46 70)
;;         (- 6 -18) (+ -47 71) (/ 120 5) (+ -48 72) (- 5 -19)
;;         (+ -49 73) (+ (+ 23 -1) 2) (+ -50 74) (- 4 -20) (+ -51 75)
;;         (/ 121 5) (+ -52 76) (- 3 -21) (+ -53 77) (+ 29 (+ -2 -3))
;;         (+ -54 78) (- 2 -22) (+ -55 79) (/ 122 5) (+ -56 80)
;;         (- 1 -23) (+ -57 81) (+ -58 82) (- 0 -24) (+ -59 83)
;;         (/ 123 5) (+ -60 84) (- -1 -25) (+ -61 85) (+ 31 (+ -3 -4))
;;         (+ -62 86) (- -2 -26) (+ -63 87) (/ 124 5) (+ -64 88)
;;         (- -3 -27) (+ -65 89) (+ (+ 27 -2) -1) (+ -66 90) (- -4 -28)
;;         (+ -67 91) (/ 144 6) (+ -68 92) (- -5 -29) (+ -69 93)
;;         (+ 33 (+ -4 -5)) (+ -70 94) (- -6 -30) (+ -71 95) (/ 145 6)
;;         (+ -72 96) (- -7 -31) (+ -73 97) (+ -74 98) (- -8 -32)
;;         (+ -75 99) (/ 146 6) (+ -76 100) (- -9 -33) (+ -77 101)
;;         (+ 35 (+ -5 -6)) (+ 79 -55) (- -10 -34) (+ -78 102)
;;         (/ 147 6) (+ -79 103) (- -11 -35) (+ -80 104)
;;         (+ (+ 26 -1) -1) (+ -81 105) (- -12 -36) (+ -82 106)
;;         (/ 148 6) (+ -83 107) (- -13 -37) (+ -84 108)
;;         (+ 37 (+ -6 -7)) (+ -85 109) (- -14 -38) (+ -86 110)
;;         (/ 149 6) (+ -87 111) (- -15 -39) (+ -88 112)))
