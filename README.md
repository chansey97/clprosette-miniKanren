# clprosette-miniKanren
A [faster-miniKanren](https://github.com/michaelballantyne/faster-minikanren) variant integrated with Rosette, inspired by [CLP(SMT)-miniKanren](https://github.com/namin/clpsmt-miniKanren).

## API

- `(rosette-typeo <var> <type)`
   Constraint a miniKanren variable as a rosette type. 
- `(rosette-asserto <formula>)`
   Check a SMT formula satisfiable.

## Running

It is not available on the Racket package server currently. Just clone the repository and play with `tests`.

### Usage

```
#lang racket
(require "../mk.rkt")
(require "../rosette-bridge.rkt")

(define (faco n out)
  (conde
    ((== n 0) (== out 1))
    ((rosette-typeo n r/@integer?)
     (rosette-asserto `(,r/@! (,r/@= ,n 0)))
     (fresh (n-1 r)
       (rosette-typeo n-1 r/@integer?)
       (rosette-typeo r r/@integer?)
       (rosette-typeo out r/@integer?)
       (rosette-asserto `(,r/@= (,r/@- ,n 1) ,n-1))
       (rosette-asserto `(,r/@= (,r/@* ,n ,r) ,out))
       (faco n-1 r)))))

(run 7 (q)
  (fresh (n out)
    (faco n out)
    (== q `(,n ,out))))
;; '((0 1) (1 1) (2 2) (3 6) (4 24) (5 120) (6 720))
```



## Why CLP(Rosette)-miniKanren?

CLP(Rosette)-miniKanren is inspired by [CLP(SMT)-miniKanren](https://github.com/namin/clpsmt-miniKanren), but provides better interactivity, extensibility, and refutation power. For example,

1. It supports true SMT type constraints (as Rosette solvable types) instead of raw ``(z/ `(declare-const ...))``.  
   - These SMT type constraints can interact with each other. In CLP(SMT)-miniKanren, you must use tags to distinguish, which is difficult to write (consider tower of types and coercion).
   - These SMT type constraints can be propagated among variables, which prevents many "unknown constant" error in CLP(SMT)-miniKanren.
   
2. It can combine Rosette constraints with miniKanren symbolic constraints (e.g. `integero`, `symbolo`, `=/=`, `absento` ) in a meaningful way. (TODO: examples to explain, e.g. constraint promotion)

3. Better reification representation. 

   Due to the lack of intermediate layers, CLP(SMT)-miniKanren cannot digest complex types (e.g. bitvector, uninterpreted function) well. You can do format conversion back forth, but it is annoying. CLP(Rosette)-miniKanren uses Rosette, so it becomes trivial.

4. It can use all the Rosette components. For example,

   - Define a Rosette function and invoke it in `rosette-asserto`. 
   - Easy to switch different SMT solvers.

     

## TODO

- [ ] Add labling for `r/purge`.
- [ ] Add tabling (two steps).
  1. Naive tabling
  2. TCLP
- [ ] Add Rosette unsolvable types support (currently only partially supported).
- [ ] Add more SMT types via extending Rosette solvable types.
- [ ] Try different search strategies with SMT (e.g. DFS with push/pop).
- [ ] Try different SMT assertion strategies (e.g. record SMT internal state? or check-smt-assumption?).
- [ ] Find killer apps and add more tests.
- [ ] Update README.



## Background
This project was inspired by Nada Amin's [CLP(SMT)-miniKanren](https://github.com/namin/clpsmt-miniKanren) and included the improvement of [smt-assumptions-full-integration](https://github.com/chansey97/faster-minikanren/tree/smt-assumptions-full-integration) which was based on [smt-assumptions](https://github.com/namin/faster-miniKanren/tree/smt-assumptions). Most of the tests in the `tests` directory initially were written in CLP(SMT)-miniKanren by Nada Amin and William Byrd.

Thank Nada Amin for bring me into [CLP(SMT)-miniKanren](https://github.com/namin/clpsmt-miniKanren). Thank Michael Ballantyne for his insightful suggestions (especially about how disequality constraint interacts with SMT constraints). Thank William Byrd joined the meeting and gave a lot of useful comments.



