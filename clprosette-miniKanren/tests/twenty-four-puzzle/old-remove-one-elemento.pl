:- use_module(library(clpfd)).

:- set_prolog_flag(answer_write_options, [max_depth(5)]).

remove_one_elemento(X, Ls, Out) :-
  [A|D] = Ls ,
  (   A = X, D = Out
  ;   dif(A,X), [A|Res] = Out,
      remove_one_elemento(X,D,Res)
  ).

%% ?- remove_one_elemento(X,[1,2,3,4],Out).
%@ X = 1,
%@ Out = [2,3,4] ;
%@ X = 2,
%@ Out = [1,3,4] ;
%@ X = 3,
%@ Out = [1,2,4] ;
%@ X = 4,
%@ Out = [1,2,3] ;
%@ false.

%% ?- remove_one_elemento(X,[1,1,2,2],Out).
%@ X = 1,
%@ Out = [1,2,2] ;
%@ X = 2,
%@ Out = [1,1,2] ;
%@ false.

numbero(X) :- var(X).
numbero(X) :- nonvar(X), number(X).

expro(Expr, NumLs, NumLsR) :-  
  numbero(Expr),
  remove_one_elemento(Expr, NumLs, NumLsR).
expro(Expr, NumLs, NumLsR) :-
  A1 + A2 = Expr,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  % 
  expro(A1, NumLs, NumLsRR),    
  expro(A2, NumLsRR, NumLsR).   
expro(Expr, NumLs, NumLsR) :-
  A1 - A2 = Expr,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  % 
  expro(A1, NumLs, NumLsRR),
  expro(A2, NumLsRR, NumLsR).
expro(Expr, NumLs, NumLsR) :-
  A1 * A2 = Expr,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  % 
  expro(A1, NumLs, NumLsRR),
  expro(A2, NumLsRR, NumLsR).
expro(Expr, NumLs, NumLsR) :-
  A1 / A2 = Expr,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  %   
  expro(A1, NumLs, NumLsRR),
  expro(A2, NumLsRR, NumLsR).

%% num-of-exps(n,o) = n! * catalan(n-1) * o^(n-1) 
%% num-of-exps(4,1) = 120
%% num-of-exps(4,1) = 960
%% num-of-exps(4,3) = 3240
%% num-of-exps(4,4) = 7680

%% ?- findall(E
%%           ,(
%%             expro(E, [1,2,3,4], [])
%%            )
%%           , Qs
%%           ), length(Qs, Len).
%@ Qs = [1+2+3+4,... + ... + 4+3,... + ... + 4,... + ...|...],
%@ Len = 7680.

%% ?- findall( E
%%           ,(
%%             expro(E, [1,1,2,2], [])
%%            )
%%           , Qs          
%%           ), length(Qs, Len).
%@ Qs = [1+1+2+2,... + ... + 1+2,... + ... + 1,... + ...|...],
%@ Len = 1920. %% simplify

%% ?- findall(E
%%           ,(
%%             expro(E, [N1,N2,N3,N4], [])
%%            )
%%           , Qs          
%%           ), length(Qs, Len).
%% @ Qs = [$VAR(...)+ $VAR(...)+ $VAR(_)+ $VAR(_),... + ... + $VAR(...)+ $VAR(_),... + ... + $VAR(...),... + ...|...],
%% @ Len = 7680. % dont run it, a lot of constraints...


%% C(52,4)＝270725, then remove duplicates = 1820

%% ?- findall([N1,N2,N3,N4]
%%           ,(
%%             N1 in 1..13
%%            ,N2 in 1..13
%%            ,N3 in 1..13
%%            ,N4 in 1..13
%%            ,N1#=<N2,N2#=<N3,N3#=<N4
%%            ,label([N1,N2,N3,N4])     
%%            )
%%           ,Qs), length(Qs,Len).
%@ Qs = [[1,1,1|...],[1,1|...],[1|...],[...|...]|...],
%@ Len = 1820.


puzzleo(Expr, NumLs, Val, NumLsR) :-
  numbero(Expr),
  Expr #= Val,
  remove_one_elemento(Expr, NumLs, NumLsR).
puzzleo(Expr, NumLs, Val, NumLsR) :-
  numbero(N1),
  numbero(N2),
  A1 + A2 = Expr,
  Val #= N1 + N2,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  % 
  puzzleo(A1, NumLs, N1, NumLsRR),
  puzzleo(A2, NumLsRR, N2, NumLsR).
puzzleo(Expr, NumLs, Val, NumLsR) :-
  numbero(N1),
  numbero(N2),
  A1 - A2 = Expr,
  Val #= N1 - N2,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  %   
  puzzleo(A1, NumLs, N1, NumLsRR),
  puzzleo(A2, NumLsRR, N2, NumLsR).
puzzleo(Expr, NumLs, Val, NumLsR) :-
  numbero(N1),
  numbero(N2),
  A1 * A2 = Expr,
  Val #= N1 * N2,
  % bounds size of NumLsRR for terminate!
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  %
  puzzleo(A1, NumLs, N1, NumLsRR),
  puzzleo(A2, NumLsRR, N2, NumLsR).
puzzleo(Expr, NumLs, Val, NumLsR) :-
  numbero(N1),
  numbero(N2),
  A1 / A2 = Expr,
  %% Val #= N1 / N2,
  0 #= N1 rem N2, Val #= N1 // N2,
  % bounds size of NumLsRR for terminate!  
  length(NumLs, LenOfNumLs),
  LenOfNumLsR in 0..sup,
  LenOfNumLsRR in 0..sup,
  LenOfNumLsRR #< LenOfNumLs,  
  LenOfNumLsR #< LenOfNumLsRR,  
  label([LenOfNumLsR, LenOfNumLsRR]),
  length(NumLsR, LenOfNumLsR),
  length(NumLsRR, LenOfNumLsRR),
  %
  puzzleo(A1, NumLs, N1, NumLsRR),
  puzzleo(A2, NumLsRR, N2, NumLsR).


%% N.B.
%% 1. This version of code is restricted to integer values, which means solutions like
%%    8/(3-(8/3))
%%    = 8/(1/3)
%%    = 24
%%    do *not* work!
%% 2. This version of code including "duplicates" solutions
%%    (1) commutative law is not considered 
%%    (2) associativity law is not considered
%%    (3) other simplifications is not considered, e.g. should we consider `a-(b+c) =?= (a-b)-c` ?

%% ?- time(
%%         (   
%%           findall(E
%%                  ,(
%%                    N1 in 1..13
%%                   ,N2 in 1..13
%%                   ,N3 in 1..13
%%                   ,N4 in 1..13
%%                   ,N1#=<N2,N2#=<N3,N3#=<N4
%%                   ,NumLs=[N1,N2,N3,N4]
%%                   ,puzzleo(E, NumLs, 24, [])
%%                   ,label(NumLs)
%%                   )
%%                  ,Qs          
%%                  ),
%%           length(Qs, Len)
%%         )
%%        ).
%@ % 17,772,341 inferences, 1.576 CPU in 1.576 seconds (100% CPU, 11279657 Lips)
%@ Qs = [1+1+9+13,... + ... + 10+12,... + ... + 11,... + ...|...],
%@ Len = 2425. % significantly improve efficiency (maybe wrong?)


%% %% test "24-puzzle-a"
%% ?- time(
%%         (
%%           findall(E
%%                  ,puzzleo(E, [1,1,1,8], 24, [])
%%                  ,Qs)
%%         ,length(Qs, Len)
%%         )
%%        ).
%@ % 14,975,620 inferences, 1.420 CPU in 1.433 seconds (99% CPU, 10549115 Lips)
%@ Qs = [(1+1+1)*8,(1+(... + ...))*8,8*(... + ...),... * ...],
%@ Len = 4.

%% test "24-puzzle-g"
%% ?- time(
%%         (
%%           findall(E
%%                  ,puzzleo(E, [2,2,10,10], 24, [])
%%                  ,Qs)
%%         , length(Qs, Len)
%%         )
%%        ).
%@ % 18,424,182 inferences, 1.778 CPU in 1.778 seconds (100% CPU, 10359910 Lips)
%@ Qs = [2+2+10+10,... + ... + 2+10,... + ... + 2,... + ...|...],
%@ Len = 36.

%% test "24-puzzle-h"
%% ?- time(
%%         (   
%%           findall(E
%%                  ,puzzleo(E, [2,2,2,12], 24, [])
%%                  ,Qs)
%%         , length(Qs, Len)
%%         )
%%        ).
%@ % 14,829,286 inferences, 1.404 CPU in 1.407 seconds (100% CPU, 10562102 Lips)
%@ Qs = [2*12-2+2,... * ... - 2+2,... - ... + ... * ...,... + ...|...],
%@ Len = 84.

%% test "24-puzzle-i"
%% ?- time(
%%         (
%%           findall(E
%%                  ,puzzleo(E, [4,6,7,7], 24, [])
%%                  ,Qs)
%%         , length(Qs, Len)
%%         )
%%        ).
%@ % 32,632,039 inferences, 3.089 CPU in 3.137 seconds (98% CPU, 10564565 Lips)
%@ Qs = [4+6+7+7,... + ... + 6+7,... + ... + 6,... + ...|...],
%@ Len = 146.


%% :- set_prolog_flag(answer_write_options, [max_depth(0)]).

%% boring!!
%% test "24-puzzle-b"
%% ?- time(
%%         (   
%%           once(
%%                findnsols(1
%%                         ,Q
%%                         ,(
%%                           N1 in 1..13
%%                          ,N2 in 1..13
%%                          ,N3 in 1..13
%%                          ,N4 in 1..13
%%                          ,[E, NumLs] = Q
%%                          ,[N1,N2,N3,N4] = NumLs
%%                          ,puzzleo(E, NumLs, 24, [])
%%                          ,label(NumLs)
%%                          )
%%                         ,Qs) 
%%               )
%%         )
%%        ).
%@ % 28,201 inferences, 0.000 CPU in 0.005 seconds (0% CPU, Infinite Lips)
%@ Qs = [[... + ... + 9+13,[1|...]]].

%% test "24-puzzle-c"
%% ?- time(
%%         (   
%%           once(
%%                findnsols(20
%%                         ,E
%%                         ,(
%%                           N1 in 2..sup
%%                          ,N2 in 2..sup
%%                          ,N3 in 2..sup
%%                          ,N4 in 2..sup
%%                          ,[N1,N2,N3,N4] = NumLs
%%                          ,puzzleo(E, NumLs, 24, [])
%%                          ,label(NumLs)
%%                          )
%%                         ,Qs) 
%%               )
%%         )
%%        ).
%@ % 19,205 inferences, 0.000 CPU in 0.002 seconds (0% CPU, Infinite Lips)
%@ Qs = [2+2+2+18,2+2+3+17,2+2+4+16,2+2+5+15,2+2+6+14,2+2+7+13,2+2+8+12,2+2+9+11,2+2+10+10,2+2+11+9,2+2+12+8,2+2+13+7,2+2+14+6,2+2+15+5,2+2+16+4,2+2+17+3,2+2+18+2,2+3+2+17,2+3+3+16,2+3+4+15].

%% test "24-puzzle-d"

%% ?- time(
%%         (   
%%           once(
%%                findnsols(10
%%                         ,E
%%                         ,(
%%                           N1 in 1..sup
%%                          ,N2 in 1..sup
%%                          ,N3 in 1..sup
%%                          ,N4 in 1..sup
%%                          ,[N1,N2,N3,N4] = NumLs
%%                          , ??? = E   % <--- TODO:  How unify operator term in Prolog?
%%                          ,puzzleo(E, NumLs, 24, [])
%%                          ,label(NumLs)
%%                          )
%%                         ,Qs) 
%%               )
%%         )
%%        ).


%% ;; (test "24-puzzle-d"
%% ;;   (run 10 (e)
%% ;;     (fresh (num* n1 n2 n3 n4 op1 op2 op3 e1 e2 e3 e4)
%% ;;       (rosette-typeo n1 r/@integer?)
%% ;;       (rosette-typeo n2 r/@integer?)
%% ;;       (rosette-typeo n3 r/@integer?)
%% ;;       (rosette-typeo n4 r/@integer?)
%% ;;       (rosette-asserto `(,r/@< 0 ,n1))
%% ;;       (rosette-asserto `(,r/@< 0 ,n2))
%% ;;       (rosette-asserto `(,r/@< 0 ,n3))
%% ;;       (rosette-asserto `(,r/@< 0 ,n4))
%% ;;       (== `(,n1 ,n2 ,n3 ,n4) num*)
%% ;;       (== `(,op1 (,op2 ,e1 ,e2) (,op3 ,e3 ,e4)) e)
%% ;;       (puzzleo e num* 24 '())))
%% ;;   '((+ (+ 21 1) (+ 1 1))
%% ;;     (+ (+ 18 2) (+ 2 2))
%% ;;     (+ (+ 15 3) (+ 3 3))
%% ;;     (+ (+ 12 4) (+ 4 4))
%% ;;     (+ (+ 16 3) (+ 3 2))
%% ;;     (+ (+ 14 5) (+ 3 2))
%% ;;     (+ (+ 13 6) (+ 3 2))
%% ;;     (+ (+ 15 3) (+ 4 2))
%% ;;     (+ (+ 14 3) (+ 5 2))
%% ;;     (+ (+ 13 5) (+ 4 2))))

%% ;; (test "24-puzzle-e"
%% ;;   (run 10 (e)
%% ;;     (fresh (num* n1 n2 n3 n4 op e1 e2)
%% ;;       (rosette-typeo n1 r/@integer?)
%% ;;       (rosette-typeo n2 r/@integer?)
%% ;;       (rosette-typeo n3 r/@integer?)
%% ;;       (rosette-typeo n4 r/@integer?)
%% ;;       (rosette-asserto `(,r/@< 0 ,n1))
%% ;;       (rosette-asserto `(,r/@< 0 ,n2))
%% ;;       (rosette-asserto `(,r/@< 0 ,n3))
%% ;;       (rosette-asserto `(,r/@< 0 ,n4))
%% ;;       (== `(,n1 ,n2 ,n3 ,n4) num*)
%% ;;       (=/= op '+)
%% ;;       (== `(,op ,e1 ,e2) e)
%% ;;       (puzzleo e num* 24 '())))
%% ;;   '((- 27 (+ 1 (+ 1 1)))
%% ;;     (- 30 (+ 2 (+ 2 2)))
%% ;;     (- 33 (+ 3 (+ 3 3)))
%% ;;     (- 36 (+ 4 (+ 4 4)))
%% ;;     (- 32 (+ 3 (+ 3 2)))
%% ;;     (- 34 (+ 5 (+ 3 2)))
%% ;;     (- 35 (+ 6 (+ 3 2)))
%% ;;     (- 33 (+ 3 (+ 4 2)))
%% ;;     (- 34 (+ 3 (+ 5 2)))
%% ;;     (- 35 (+ 5 (+ 4 2)))))

%% ;; (test "24-puzzle-f"
%% ;;   (run 10 (e)
%% ;;     (fresh (num* n1 n2 n3 n4 op e1 e2)
%% ;;       (rosette-typeo n1 r/@integer?)
%% ;;       (rosette-typeo n2 r/@integer?)
%% ;;       (rosette-typeo n3 r/@integer?)
%% ;;       (rosette-typeo n4 r/@integer?)
%% ;;       (rosette-asserto `(,r/@< 0 ,n1))
%% ;;       (rosette-asserto `(,r/@< 0 ,n2))
%% ;;       (rosette-asserto `(,r/@< 0 ,n3))
%% ;;       (rosette-asserto `(,r/@< 0 ,n4))
%% ;;       (== `(,n1 ,n2 ,n3 ,n4) num*)
%% ;;       (== op '*)
%% ;;       (== `(,op ,e1 ,e2) e)
%% ;;       (puzzleo e num* 24 '())))
%% ;;   '((* 2 (+ 2 (+ 4 6)))
%% ;;     (* 1 (+ 8 (+ 12 4)))
%% ;;     (* 3 (+ 1 (+ 4 3)))
%% ;;     (* 6 (+ 2 (+ 1 1)))
%% ;;     (* 1 (+ 16 (+ 1 7)))
%% ;;     (* 1 (+ 16 (+ 5 3)))
%% ;;     (* 1 (+ 2 (+ 16 6)))
%% ;;     (* 1 (+ 16 (+ 4 4)))
%% ;;     (* 2 (+ 3 (+ 8 1)))
%% ;;     (* 1 (+ 16 (+ 2 6)))))


