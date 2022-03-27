#lang racket
(require "../../../rosette/rosette/base/core/term.rkt")
(require "../../../rosette/rosette/base/core/type.rkt")
(require "../../../rosette/rosette/base/form/define.rkt")

(require "../../../rosette/rosette/solver/solver.rkt")
(require "../../../rosette/rosette/solver/solution.rkt")
(require "../../../rosette/rosette/solver/smt/z3.rkt")
(require (only-in "../../../rosette/rosette/solver/smt/server.rkt" output-smt))

(require (prefix-in r/ "../../../rosette/rosette/base/core/equality.rkt"))
(require (prefix-in r/ "../../../rosette/rosette/base/core/bool.rkt"))
(require (prefix-in r/ "../../../rosette/rosette/base/core/real.rkt"))

(require "../../../rosette/rosette/query/core.rkt") ; current-solver
;; (require "../../../rosette/rosette/query/finitize.rkt")

(require "../../logging.rkt")
(require "../../test-check.rkt")
(require "../../mk.rkt")

;; (current-bitwidth 8)
;; (output-smt "./")
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

(run 1 (q)
  (fresh (x)
    (rosette-typeo q r/@boolean?)
    (let ()
      (define-symbolic* rx r/@boolean?)
      (rosette-asserto `(,r/@forall (,rx) (,r/|| ,rx ,q))))))

;; A problem of forall:
;; In Z3 version 4.8.7, get-model returns
;; (model
;;   (define-fun c1 () Bool
;;     true)
;; )
;; However, in z3 version 4.8.12, get-model returns
;; (
;;   (define-fun e3 () Bool
;;     (forall ((c0 Bool)) (or c0 c1)))
;;   (define-fun c1 () Bool
;;     true)
;; )
;; So in z3 version 4.8.12, Rosette complains:
;; ; Unrecognized symbol:  'forall

;; TODO:
;; Maybe customize own solver
;; https://github.com/emina/rosette/issues/122#issuecomment-474108388
