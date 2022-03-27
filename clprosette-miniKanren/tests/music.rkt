(load "require.scm")

(define perfect-consonant '(0 5 7))
(define consonant '(0 3 4 5 7 8 9))
(define imperfect-consonant '(3 4 8 9))

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
         (smt-typeo note 'Int)
         (smt-typeo harmony 'Int)
         (conde
          ((smt-asserto `(= (- ,note ,harmony) ,d)))
          ((smt-asserto `(not (= (- ,note ,harmony) ,d)))
           (interval-ino dr note harmony)))))

(define (ino xs x)
  (fresh (y ys)
         (== (cons y ys) xs)
         (smt-typeo x 'Int)
         (smt-typeo y 'Int)
         (conde
          ((smt-asserto `(= ,x ,y)))
          ((smt-asserto `(not (= ,x ,y)))
           (ino ys x)))))

(define (nexto harmony prev-harmony cur-harmony)
  (fresh (p hs cs)
         (== (cons `(,p ,cs) hs) harmony)
         (smt-typeo p 'Int)
         (smt-typeo prev-harmony 'Int)
         (conde
          ((smt-asserto `(= ,p ,prev-harmony))
           (ino cs cur-harmony))
          ((smt-asserto `(not (= ,p ,prev-harmony)))
           (nexto hs prev-harmony cur-harmony)))))

(define (zico measure phrase position prev-note cur-note prev-harmony cur-harmony)
  (fresh ()
         (nexto harmony prev-harmony cur-harmony)
         (smt-typeo position 'Int)
         (smt-typeo measure 'Int)
         (conde
          ((smt-asserto `(= 0 (mod ,position ,measure)))
           (== cur-harmony 1)
           (interval-ino perfect-consonant cur-note cur-harmony))
          ((smt-asserto `(not (= 0 (mod ,position ,measure))))
           (interval-ino imperfect-consonant cur-note cur-harmony)))))

(define (musico measure phrase position prev-note prev-harmony m)
  (fresh ()
         (smt-typeo position 'Int)
         (smt-typeo measure 'Int)
         (smt-typeo phrase 'Int)
         (conde
          ((smt-asserto `(= ,position ,(* measure phrase)))
           (== m '()))
          ((smt-asserto `(< ,position ,(* measure phrase)))
           (fresh (position+1 cur-note cur-harmony rest-m)
                  (== m (cons (list cur-note cur-harmony) rest-m))
                  (smt-typeo position+1 'Int)
                  (smt-asserto `(= ,position+1 (+ 1 ,position)))
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
