(define z3-counter-check-sat 0)
(define z3-counter-get-model 0)

(define log-all-calls #f)
;; (define log-all-calls #t)

(define log-all-calls-with-file #f)
;; (define log-all-calls-with-file #t)

(define z3-unknown-robust #f)
;; (define z3-unknown-robust #t)

;; (define z3-version 'z3-4.8.7)
(define z3-version 'z3-4.8.12)

(define z3-params '(;; smt.arith.solver:
                    ;; default:0
                    "smt.random_seed=1"
                    ;; "smt.random_seed=2"
                    ;; "smt.random_seed=3"
                    
                    ;; smt.arith.solver:
                    ;; default:2 in z3-4.8.7
                    ;; default:6 in z3-4.8.12
                    ;; "smt.arith.solver=1"
                    ;; "smt.arith.solver=2"
                    "smt.arith.solver=6"
                    ))

(define (z3-process-start)
  (open-process-ports (string-append "z3 -in " (fold-right (lambda (x y) (string-append x " " y)) "" z3-params))
                      'block
                      (native-transcoder)))
(define-values (z3-out z3-in z3-err z3-p)
  (z3-process-start))
;; (define (z3-reset!)
;;   (let-values (((out in err p)
;;                 (z3-process-start)))
;;     (set! z3-out out)
;;     (set! z3-in in)
;;     (set! z3-err err)
;;     (set! z3-p p)))
(define (z3-check-in!)
  (if (eof-object? z3-in)
      (error 'z3-check-in "z3 input port")
      ;; (if (= 0 (mod z3-counter-check-sat 300))
      ;;     (z3-reset!)
      ;;     #t)
      #t))

(define read-sat
  (lambda ()
    (z3-check-in!)
    (let ([r (read z3-in)])
      (when log-all-calls-with-file
        (let ((p^ (open-output-file "log.smt" 'append)))
          (fprintf p^ "~a\n" r)
          (flush-output-port p^)
          (close-output-port p^)))
      (when log-all-calls (printf/debug "read-sat: ~a\n" r))
      (if (eq? r 'sat)
          #t
          (if (eq? r 'unsat)
              #f
              (if (eq? r 'unknown)
                  (begin
                    (printf/warning "read-sat: unknown\n")
                    (when z3-unknown-robust (z/gc!))
                    #f)
                  (error 'read-sat (format "~a" r))))))))

(define (init-log)
  (when log-all-calls-with-file
    (let ((p (open-output-file "log.smt" 'replace)))
      (close-output-port p))))

;; TODO: Support other types, e.g. Bitvector, etc.
;; May using string instead of symbol.
(define scheme->smt
  (lambda (e)
    (cond
      ((pair? e) (cons (scheme->smt (car e)) (scheme->smt (cdr e))))
      ((eq? e #t) 'true)
      ((eq? e #f) 'false)
      (else e))))

(define call-z3
  (lambda (xs)
    (when log-all-calls (printf/debug "call-z3 enter: xs = ~a\n" xs))
    (let ((xs (scheme->smt xs)))
      (when log-all-calls-with-file
        (let ((p^ (open-output-file "log.smt" 'append)))
          (for-each (lambda (x)
                      (fprintf p^ "~a\n" x)) xs)
          (flush-output-port p^)
          (close-output-port p^)))
      (for-each (lambda (x)
                  (when log-all-calls (printf/debug "~a\n" x))
                  (fprintf z3-out "~a\n" x)) xs)
      (flush-output-port z3-out))
    ))


(define read-model
  (lambda ()
    (let ([m (read z3-in)])
      (when log-all-calls-with-file
        (let ((p^ (open-output-file "log.smt" 'append)))
          (if (eq? z3-version 'z3-4.8.12)
              (if (pair? m)
                  (begin
                    (fprintf p^ "(\n")
                    (for-each (lambda (x)
                                (fprintf p^ "  ~a\n" x)) m)
                    (fprintf p^ ")\n"))
                  (fprintf p^ "~a\n" m))
              (if (equal? (car m) 'model)
                  (begin
                    (fprintf p^ "(\n")
                    (fprintf p^ "  model\n")
                    (for-each (lambda (x)
                                (fprintf p^ "  ~a\n" x)) (cdr m))
                    (fprintf p^ ")\n"))
                  (fprintf p^ "~a\n" m)))
          (flush-output-port p^)
          (close-output-port p^)))
      (when log-all-calls (printf/debug "~a\n" m))
      (map (lambda (x)
             (let ((id (cadr x))
                   (params (caddr x))
                   (type (cadddr x))
                   (val (car (cddddr x)) ))
               (let ((val (cond
                            ((eq? val 'false) #f)
                            ((eq? val 'true) #t)
                            (else (eval val)))))
                 (list id val type))
               ))
           (filter (lambda (x)
                     ;; We currently don't support functions, so we shouldn't get a model which includes functions 
                     ;; NOTE: z3-4.8.12 will return functions, even if we don't use functions.                     
                     (let ((params (caddr x)))
                       (cond
                         ((null? params) #t)
                         (else
                          (if (eq? z3-version 'z3-4.8.12)
                              #f
                              (error 'read-model "doesn't support functions params" params))))))
                   (if (eq? z3-version 'z3-4.8.12)
                       m
                       (cdr m)))
           ))))

(define get-model-inc
  (lambda ()
    (call-z3 '((get-model)))
    (set! z3-counter-get-model (+ z3-counter-get-model 1))
    (read-model)))


(define neg-model
  (lambda (model)
    (cons
        'assert
      (list
       (cons
           'or
         (map
          (lambda (xv)
            (let ((id (car xv))
                  (val (cadr xv))
                  (type (caddr xv)))
              `(not (= (as ,id ,type) ,val))
              )) model))))
    ))

