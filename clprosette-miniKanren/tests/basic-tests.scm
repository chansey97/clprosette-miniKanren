
(test "==-and-smt:"
      (run 1 (q)
           (fresh (a b)
                  (== a b)
                  (smt-typeo a 'Int) ;
                  (smt-asserto `(= ,a 5))
                  ))
      '(_.0))

(test "==-and-smt: duplicate declare"
      (run 1 (q)
           (fresh (a b)
                  (== a b)
                  (smt-typeo a 'Int)
                  (smt-asserto `(= ,a 5))
                  (smt-typeo b 'Int)
                  ))
      '(_.0))

(test "==-and-smt: fix a bug when gc-assumption-threshold = 1"
      (run 3 (q)
           (conde
            ((fresh (x)
                    (smt-typeo x 'Int)
                    (smt-asserto `(= ,x 1))))
            ((fresh (x)
                    (smt-typeo x 'Int)
                    (smt-asserto `(= ,x 2))))
            ))
      '(_.0 _.0))

(test "==-and-smt: duplicate declare in conde, and fix a bug when gc-assumption-threshold = 1"
      (run 3 (q)
           (conde
            ((smt-typeo q 'Int)
             (smt-asserto `(= ,q 1)))
            ((smt-typeo q 'Int)
             (smt-asserto `(= ,q 2)))
            ))
      '(1 2))

(test "boolean"
      (run 1 (q)
           (fresh (a b)
                  (== a b)
                  (smt-typeo a 'Bool)
                  (smt-asserto `(= ,a #f))
                  (== q `(,a ,b))))
      '((#f #f)))

;; https://github.com/namin/clpsmt-miniKanren/issues/10

;; Declare a fresh variable at the top
(define add1o
  (lambda (n out)
    (fresh ()
           (smt-asserto `(= ,out (+ ,n 1))))))

(test ""
      (run 5 (q)
           (fresh (n out)
                  (smt-typeo n 'Int)
                  (smt-typeo out 'Int)
                  (add1o n out)
                  (== q `(,n ,out))))
      '((0 1) (1 2) (2 3) (3 4) (4 5)))

(test ""
      (run 5 (q)
           (fresh (n)
                  (smt-typeo n 'Int)
                  (add1o n 1)
                  (== q n)))
      '(0))

(test ""
      (run 5 (q)
           (fresh (out)
                  (smt-typeo out 'Int)
                  (add1o 1 out)
                  (== q out)))
      '(2))

;; Declare a variable, but that variable has already been unified with a constant.
(define add1o
  (lambda (n out)
    (fresh ()
           (smt-typeo n 'Int)
           (smt-typeo out 'Int)
           (smt-asserto `(= ,out (+ ,n 1))))))

(test ""
      (run 5 (q)
           (fresh (n out)
                  (add1o n out)
                  (== q `(,n ,out))))
      '((0 1) (-1 0) (-2 -1) (-3 -2) (-4 -3)))

(test ""
      (run 5 (q)
           (fresh (n)
                  (add1o n 1)
                  (== q n)))
      '(0))

(define (nevero)
  (conde
   [(== 1 2)]
   [(nevero)]))

(test ""
      (run 1 (q)
           (fresh (a b)
                  (smt-typeo a 'Int)
                  (smt-asserto `(= ,a 5))
                  
                  (smt-typeo b 'Int)
                  (smt-asserto `(= ,b 6))
                  
                  (== a b) ; <-- promote the `==` to SMT assert
                  
                  (nevero)))
      '())

(define (nevero)
  (conde
   [(== 1 2)]
   [(nevero)]))

(test ""
      (run 1 (q)
           (fresh (a b)
                  (=/= a b)
                  
                  (smt-typeo a 'Int)
                  (smt-asserto `(= ,a 5))
                  
                  (smt-typeo b 'Int)
                  (smt-asserto `(= ,b 5)) ; <-- promote the above `=/=` to SMT assert
                  
                  (nevero)))
      '())

(test ""
      (run 3 (q)
           (fresh (a b)
                  (=/= a b)
                  (smt-typeo a 'Int)
                  (smt-asserto `(= ,a 5)) ; <-- won't actually promote the above `=/=` to SMT assert, because b is not a SMT variable
                  (== q `(,a ,b))))
      '(((5 _.0) (=/= ((_.0 5))))))

(define (nevero)
  (conde
   [(== 1 2)]
   [(nevero)]))

(test ""
      (run 1 (q)
           (fresh (a b)

                  (smt-typeo a 'Int)
                  (smt-asserto `(= ,a 5))

                  (smt-typeo b 'Int)
                  (smt-asserto `(= ,b 5))
                  
                  (=/= a b) ; <-- promote the `=/=` to SMT assert 
                  
                  (nevero)))
      '())

(test "refute"
      (run 1 (q)
           (fresh (a b)
                  (=/= a b)
                  (smt-typeo a 'Int)
                  (smt-typeo b 'Int)
                  (smt-asserto `(= (- ,a ,b) 0))  ; <-- promote the above `=/=` to SMT assert 
                  ))
      '())

(define (nevero)
  (conde
   [(== 1 2)]
   [(nevero)]))

(test ""
      (run 1 (q)
           (fresh (a b c d)
                  (=/= (list a b) (list c d))

                  (smt-typeo a 'Int)
                  (smt-typeo c 'Int)
                  (smt-asserto `(< ,a 2))
                  (smt-asserto `(> ,a 0))
                  (smt-asserto `(= ,c 1))

                  (== b d)
                  
                  (nevero)
                  ))
      '())

(test ""
      (run 3 (q)
           (fresh (a b c d e f)
                  (=/= (list a b c) (list d e f))

                  (smt-typeo b 'Int)
                  (smt-typeo e 'Int)
                  (smt-asserto `(< ,b 2))
                  (smt-asserto `(> ,b 0))
                  (smt-asserto `(= ,e 1))
                  
                  (== a d)
                  (== c f)
                  ))
      '())

(test ""
      (run 3 (q)
           (fresh (a b c d e f)
                  (=/= (list a b c) (list d e f))

                  (smt-typeo b 'Int)
                  (smt-typeo e 'Int)
                  (smt-asserto `(< ,b 2))
                  (smt-asserto `(> ,b 0))
                  (smt-asserto `(= ,e 1))
                  
                  (== a d)
                  
                  (== q `((,a ,b ,c) (,d ,e ,f)))
                  ))
      '((((_.0 1 _.1) (_.0 1 _.2)) (=/= ((_.1 _.2))))))

;; Some normal tests for `=/=`
(test ""
      (run 1 (q)
           (fresh (x)
                  (=/= x 0)
                  (== q x)
                  ))
      '((_.0 (=/= ((_.0 0))))))

(test ""
      (run 1 (q)
           (fresh (x)
                  (=/= x 0)
                  (== q x)
                  ))
      '((_.0 (=/= ((_.0 0))))))

(test ""
      (run 1 (q)
           (fresh (x)
                  (=/= x 0)
                  (== x q)
                  ))
      '((_.0 (=/= ((_.0 0))))))


(test ""
      (run 1 (q)
           (fresh (x a b)
                  (=/= a b)
                  (== a `(,x 111 222))
                  (== b `(0 111 222))
                  (== q x)
                  ))
      '((_.0 (=/= ((_.0 0))))))

(test ""
      (run 1 (q)
           (fresh (x a b)
                  (=/= a b)
                  (== a `(,x 111 222))
                  (== b `(0 111 222))
                  (== x q)
                  ))
      '((_.0 (=/= ((_.0 0))))))


;; An example of SMT type propagation
(test "==-and-smt: type propagration"
      (run 1 (q)
           (fresh (a b)
                  (smt-typeo a 'Int)
                  (smt-asserto `(= ,a 5))
                  
                  (== a b)
                  (== q `(,a ,b))))
      '((5 5)))


;; smt-typeo is not z/
(test "smt-typeo-0"
      (run 3 (q)
           (smt-typeo q 'Int))
      '(0 2 3))

;; ex1
(test "smt-typeo-1"
      (run 3 (q)
           (fresh (a b)
                  (smt-typeo a 'Int)
                  (== a #f)
                  ))
      '())

(test "smt-typeo-2"
      (run 3 (q)
           (fresh (a b)
                  (smt-typeo a 'Int)
                  (smt-typeo b 'Bool)
                  (== a b)
                  ))
      '())

(test "smt-typeo-3"
      (run 3 (q)
           (fresh (a b)
                  (smt-typeo a 'Int)
                  (smt-typeo b 'Bool)
                  (== a b)
                  ))
      '())

(test "smt-typeo-4"
      (run 3 (q)
           (fresh (a b) 
                  (smt-typeo b 'Int)
                  (== a b)
                  ))
      '(_.0 _.0 _.0))

(test "smt-typeo-5"
      (run 3 (q)
           (fresh (a b)
                  (smt-typeo b 'Bool)
                  (== a b)
                  (smt-typeo a 'Int)
                  ))
      '())

(test "smt-typeo-6"
      (run 3 (q)
           (fresh (a b)
                  (smt-typeo b 'Bool)
                  (== a b)
                  (== a 1)
                  ))
      '())

;; ex2
(test "smt-typeo-7"
      (run 3 (q)
           (fresh (a)
                  (smt-typeo a 'Int)
                  (symbolo a)))
      '())

(test "smt-typeo-8"
      (run 3 (q)
           (fresh (a)
                  (symbolo a)
                  (smt-typeo a 'Int)
                  ))
      '())

(test "smt-typeo-9"
      (run 3 (q)
           (fresh (a)
                  (numbero a)
                  (smt-typeo a 'Int)
                  ))
      '(_.0 _.0 _.0))

(test "smt-typeo-10"
      (run 3 (q)
           (fresh (a)
                  (smt-typeo a 'Int)
                  (numbero a)
                  ))
      '(_.0 _.0 _.0))


(test "smt-typeo-11"
      (run 3 (q)
           (fresh (a)
                  (smt-typeo a 'Int)
                  (smt-typeo a 'Real)
                  ))
      '())

(test "smt-typeo-12"
      (run 3 (q)
           (fresh (a)
                  (numbero a)
                  (smt-typeo a 'Int)
                  (smt-typeo a 'Real)
                  ))
      '())

;; conde
(test "conde-1"
      (run 3 (q)
           (conde
            ((smt-typeo q 'Int)
             (smt-asserto `(= ,q 1)))
            ((smt-typeo q 'Bool)
             (smt-asserto `(= ,q #t)))
            ))
      '(1 #t))

(test "conde-1: qualified identifiers"
      (run 3 (q)
           (conde
            ((smt-typeo q 'Int)
             (smt-asserto `(= (as ,q Int)  1)))
            ((smt-typeo q 'Bool)
             (smt-asserto `(= (as ,q Bool) #t)))
            ))
      '(1 #t))

(test "conde-2"
      (run 3 (q)
           (conde
            ((smt-typeo q 'Int)
             (smt-asserto `(= ,q 1)))
            ((smt-typeo q 'Real)
             (smt-asserto `(= ,q 2.0)))
            ))
      '(1 2.0))

(test "=/=-promotion-1"
      (run 1 (q)
           (fresh (x y)
                  (smt-typeo x 'Int)
                  (=/= x 1)
                  (=/= x 2)
                  ))
      '(_.0))

(test "=/=-promotion-2"
      (run 1 (q)
           (fresh (x y)
                  (smt-typeo x 'Int)
                  (smt-typeo y 'Bool)
                  (=/= x y)))
      '(_.0))
