;; http://www.dmi.unipg.it/~formis/papers/JETAI07.pdf
;; p. 7
;; problem in CLP(FD)
;; (1)  coloring(K, Vars) :-
;; (2)    graph(Nodes, Edges),length(Nodes,N),
;; (3)    length(Vars,N),
;; (4)    domain(Vars, 1, K),
;; (5)    constraints(Edges, Nodes, Vars),
;; (6)    labeling([ff], Vars).
;; (7)  constraints([],_,_).
;; (8)  constraints([[A,B]|R], Nodes, Vars) :-
;; (9)    nth(IdfA,Nodes,A),nth(IdfA,Vars,ColA),
;; (10)   nth(IdfB,Nodes,B),nth(IdfB,Vars,ColB),
;; (11)   ColA #\= ColB,
;; (12)   constraints(R, Nodes, Vars).
;;
;; graph([1,2,3],[[1,2],[1,3],[2,3]]),

(define (grapho nodes edges)
  (fresh ()
         (== nodes '(1 2 3))
         (== edges '((1 2) (1 3) (2 3)))))

(define (coloringo k vars)
  (fresh (nodes edges n)
         (grapho nodes edges)
         (lengtho nodes n)
         (lengtho vars n)
         (for-eacho vars
                    (lambda (v)
                      (fresh ()
                             (smt-typeo v 'Int)
                             (smt-typeo k 'Int)
                             (smt-asserto `(<= 1 ,v))
                             (smt-asserto `(<= ,v ,k)))))
         (constraintso edges nodes vars)
         ))

(define (constraintso edges nodes vars)
  (conde
   ((== edges '()))
   ((fresh (a b r idfa idfb cola colb)
           (== edges `((,a ,b) . ,r))
           (=/= cola colb)
           (smt-typeo cola 'Int)
           (smt-typeo colb 'Int)
           (smt-asserto `(not (= ,cola ,colb)))
           (ntho idfa nodes a) (ntho idfa vars cola)
           (ntho idfb nodes b) (ntho idfb vars colb)
           (constraintso r nodes vars)))))

(define (ntho i xs x)
  (fresh (y ys)
         (== `(,y . ,ys) xs)
         (smt-typeo i 'Int)
         (conde
          ((== i 0) (smt-asserto `(= ,i 0))
                    (== y x))
          ((=/= i 0)
           (fresh (i-1)
                  (smt-typeo i-1 'Int)
                  (smt-asserto `(= ,i (+ ,i-1 1)))
                  (ntho i-1 ys x))))))

(define (for-eacho vars ro)
  (conde
   ((== vars '()))
   ((fresh (x rest)
           (== `(,x . ,rest) vars)
           (ro x)
           (for-eacho rest ro)))))


(define (lengtho xs n)
  (fresh ()
         (smt-typeo n 'Int)
         (smt-asserto `(>= ,n 0))
         (conde
          ((== xs '()) (== n 0) (smt-asserto `(= ,n 0)))
          ((fresh (x rest n-1)
                  (smt-typeo n-1 'Int)
                  (== `(,x . ,rest) xs)
                  (smt-asserto `(= ,n (+ ,n-1 1)))
                  (lengtho rest n-1))))))

;; non-deterministic result :(
#;
(test "3coloring"
      (run* (q) (coloringo 3 q))
      '((3 2 1) (3 1 2) (2 3 1) (1 3 2) (1 2 3) (2 1 3)))
