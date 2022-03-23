;; (define gc-assumption-threshold 10000000)
;; (define gc-assumption-threshold 1000) ; original
;; (define gc-assumption-threshold 250)
;; (define gc-assumption-threshold 100)
;; (define gc-assumption-threshold 50)
(define gc-assumption-threshold 25)
;; (define gc-assumption-threshold 1)

(define partition
  (lambda (p xs)
    (cons (filter p xs)
      (filter (lambda (x) (not (p x))) xs))))

(define declare-datatypes?
  (lambda (s)
    (and (pair? s)
         (or (eq? 'declare-datatypes (car s))
             (eq? 'declare-sort (car s)))
         (cadr s))))

(define declares?
  (lambda (s)
    (and (pair? s)
         (or (eq? 'declare-fun (car s))
             (eq? 'declare-const (car s)))
         )))

(define remove-redundant-declares
  (lambda (ds)
    (remove-duplicates ds)))

(define remove-declares*
  (lambda (ds^ ds)
    (remove* ds^ ds)))

(define decls '())
(define undeclared?!
  (lambda (x)
    (let ((r (not (member x decls))))
      (when r
        (set! decls (cons x decls)))
      r)))

; (Var) -> Symbol
(define (reify-v-name v)
  (string->symbol
   (string-append "_v" (number->string (var-idx v)))))

; (Term) -> SExpr
; replaces all miniKanren variables in a term with symbols like _v0 for the solver.
(define (reify-to-smt-symbols v)
  (cond
    ((var? v) (reify-v-name v))
    ((pair? v)
     (cons (reify-to-smt-symbols (car v)) (reify-to-smt-symbols (cdr v))))
    (else v)))

(define vars/smt-type
  (lambda (e acc)
    (cond
      ((pair? e)
       (cond
         ((or (eq? (car e) 'as)
              (eq? (car e) 'declare-const))
          (let ((v (cadr e))
                (t (caddr e)))
            (cond
              ((var? v) (cons (list v t) acc))
              (else acc))
            ))
         (else
          (vars/smt-type (cdr e) (vars/smt-type (car e) acc)))))
      (else acc))))

(define z/reify-SM
  (lambda (M . args)
    (let ((no_walk? (and (not (null? args)) (car args))))
      (lambda (st)
        (let* ((S (state-S st))
               (M (reverse M))
               (M (if no_walk? M (walk* M S)))
               (vs (vars/smt-type M '()))
               (M (reify-to-smt-symbols M))
               (dd-M (partition declare-datatypes? M))
               (dd (car dd-M))
               (M (cdr dd-M))
               (ds-R (partition declares? M))
               (ds (car ds-R))
               (R (cdr ds-R)))
          (list
           dd
           ds
           R
           vs))))))

(define (get-assumptions a)
  (let ((pos (assq a assumption-chains)))
    (map (lambda (b)
           (if (memq b pos)
               b
               `(not ,b)))
         (reverse all-assumptions))))
(define (check-sat-assuming a m)
  (replay-if-needed a m)
  (call-z3 `((check-sat-assuming ,(get-assumptions a))))
  (read-sat))

(define rewrite-assertion
  (lambda (e st)
    (cond
      ((var? e)
       (let* ((S (state-S st))
              (e^ (walk* e S)))
         (cond
           ((var? e^)
            (let* ((c (lookup-c e^ st))
                   (M (c-M c)))
              (cond
                ((not M) (error 'rewrite-assertion "All the variables must be smt-typeo first!" e))
                (else `(as ,e ,M)))))
           (else e)))
       )
      ((pair? e)
       (cond
         ((eq? (car e) 'as)
          (let ((v (cadr e))
                (t (caddr e)))
            (let* ((S (state-S st))
                   (v^ (walk* v S)))
              (cond
                ((var? v^)
                 (let* ((c (lookup-c v^ st))
                        (M (c-M c)))
                   (cond
                     ((not M)
                      (error 'rewrite-assertion "All the variables must be smt-typeo first!" e))
                     (else
                      (cond
                        ((not (equal? M t))
                         (error 'rewrite-assertion "inconsistent with qualified variable" e))
                        (else e))))))
                (else v^)))))
         (else
          (cons (rewrite-assertion (car e) st) (rewrite-assertion (cdr e) st)))))
      (else e))))

(define smt-asserto/internal
  (lambda (e)
    (lambdag@ (st)
              (let ((e (rewrite-assertion e st)))
                (if e ((z/assert e) st) #f))
              )))

(define smt-asserto
  (lambda (e)
    (lambdag@ (st)
              ((smt-asserto/internal e) st)
              )))

(define z/type->pred
  (lambda (smt-type)
    (cond
      ((equal? smt-type 'Int)
       (lambda (x) (and (number? x) (exact? x))))
      ((equal? smt-type 'Real)
       (lambda (x) (and (number? x) (not (exact? x)))))
      ((equal? smt-type 'Bool)
       (lambda (x) (boolean? x)))
      (else (error 'z/type->pred "not support type" smt-type)))))

(define smt-typeo/internal
  (lambda (u smt-type)
    (lambdag@ (st)
              (let ((type-pred (z/type->pred smt-type))
                    (term (walk u (state-S st))))
                (cond
                  ((type-pred term) st)
                  ((var? term)
                   (let* ((c (lookup-c term st))
                          (M (c-M c))
                          (T (c-T c))
                          (D (c-D c)))
                     (cond ((not T)
                            (cond
                              ((not M) (bind* st
                                              (lambdag@ (st) (set-c term (c-with-M c smt-type) st))
                                              (z/ `(declare-const ,term ,smt-type))
                                              (z/assert `(= (as ,term ,smt-type) (as ,term ,smt-type)))
                                              (if (null? D) ; trigger delayed =/=, if (null? D)
                                                  (lambdag@ (st) st)
                                                  (lambdag@ (st) ((add-smt-disequality D) st)))
                                              ))
                              ((eq? M smt-type) st)
                              (else #f)))
                           ((eq? T 'numbero)
                            (cond
                              ((not M)
                               (cond
                                 ((or (eq? smt-type 'Int) (eq? smt-type 'Real))  ; M = #f, and smt-type = Int or Real
                                  (bind* st
                                         (lambdag@ (st) (set-c term (c-with-M c smt-type) st))
                                         (z/ `(declare-const ,term ,smt-type))
                                         (z/assert `(= (as ,term ,smt-type) (as ,term ,smt-type)))
                                         (if (null? D) ; trigger delayed =/=, if (null? D)
                                             (lambdag@ (st) st)
                                             (lambdag@ (st) ((add-smt-disequality D) st)))
                                         ))
                                 (else #f)  ; M = #f, and smt-type != Int or Real
                                 ))
                              ((or (eq? M 'Int) (eq? M 'Real))
                               (if (eq? M smt-type) st #f) ) ; M is Int or Real
                              (else #f) ; M != Int or Real, or smt-type != Int or Real
                              ))
                           (else #f) ; T is not numbero
                           )
                     ))
                  (else #f)))
              )))

(define smt-typeo
  (lambda (u smt-type)
    (lambdag@ (st)
              ((smt-typeo/internal u smt-type) st)
              )))

(define (add-smt-equality v t m)
  (lambdag@ (st)
            (bind*
             st
             (smt-typeo/internal t m)
             (lambda (st)
               (if (var? t)
                   ((z/assert `(= (as ,v ,m) (as ,t ,m)) #t) st)
                   ((z/assert `(= (as ,v ,m) ,t) #t) st))))
            ))

(define (get-smt-type st x)
  (cond
    ((number? x) 'Int)
    ((boolean? x) 'Bool)
    ((var? x)
     (let ((c (lookup-c x st)))
       (c-M c)))
    (else #f)))

(define (smt-ok? st x y)
  (let ((x (walk* x (state-S st)))
        (y (walk* y (state-S st))))
    (let ((x-type (get-smt-type st x))
          (y-type (get-smt-type st y)))
      (if (or (eq? x-type #f) (eq? y-type #f)) #f
          (equal? x-type y-type)))))

(define (filter-smt-ok? st D)
  (filter
   (lambda (cs)
     (for-all (lambda (ds)
                (smt-ok? st (car ds) (cdr ds)))
              cs))
   D))

(define (add-smt-disequality D)
  (lambdag@ (st)
            (let ((as (filter-smt-ok? st D)))
              (if (not (null? as))
                  ((smt-asserto/internal
                    `(and
                      ,@(map
                         (lambda (cs)
                           `(or
                             ,@(map
                                (lambda (ds)
                                  `(not (= ,(car ds) ,(cdr ds))))
                                cs))) as))) st)
                  st)
              )))

(define global-buffer '())
(define z/global
  (lambda (lines)
    (call-z3 lines)
    (set! global-buffer (append global-buffer lines))))
(define local-buffer '())
(define z/local
  (lambda (ds R)
    (lambdag@ (st)
              (bind*
               st
               (lambda (st)
                 ;; set the branch M
                 ;; FIXME: is it possible there is duplicate declare already in the branch M? 
                 (let* ((lines (append ds R))
                        (M (append (reverse lines) (state-M st))))
                   (state-with-M st M)))
               (lambda (st)
                 ;; call z3
                 ;; If decls already has declares in ds, remove the declares in ds
                 (let ((ds (remove-declares* decls ds)))
                   (set! decls (append ds decls))
                   (let* ((lines (append ds R)))
                     (set! local-buffer (append local-buffer lines))
                     (call-z3 lines)
                     st)
                   ))))))
(define (replay-if-needed a m)
  (let ((r (filter (lambda (x) (not (member x local-buffer))) m)))
    (unless (null? r)
      (let ((lines (reverse r)))
        (let ((new-decls  (filter (lambda (x)
                                    (and (declares? x)
                                         (not (equal? (substring (symbol->string (cadr x)) 0 2) "_a"))))
                                  lines))
              (new-assumptions (filter (lambda (x)
                                         (and (declares? x)
                                              (equal? (substring (symbol->string (cadr x)) 0 2) "_a")
                                              (eq? (caddr x) 'Bool)))
                                       lines))
              (other-lines (filter (lambda (x) (not (declares? x))) lines)))
          (let* ((undeclared-decls (filter (lambda (x) (undeclared?! x)) new-decls))
                 (undeclared-assumptions (filter (lambda (x) (undeclared?! x)) new-assumptions))
                 (undeclared-rs
                  (if (eq? a 'true)
                      '()
                      (let* ((p (assq a relevant-vars))
                             (vs (cdr p))
                             (vs-decls (map (lambda (v/t) `(declare-const ,(reify-v-name (car v/t)) ,(cadr v/t))) vs)))
                        (filter undeclared?! vs-decls)))))
            (let* ((undeclared-decls/rs (append undeclared-rs undeclared-decls))
                   (undeclared-decls/rs (remove-redundant-declares undeclared-decls/rs))
                   (actual-lines (append undeclared-decls/rs undeclared-assumptions other-lines)))
              (set! all-assumptions (append (map cadr undeclared-assumptions) all-assumptions))
              (set! local-buffer (append local-buffer actual-lines))            
              (call-z3 actual-lines)
              )))))))

(define (z/check m a no_walk?)
  (lambdag@ (st)
            (begin
              (replay-if-needed (last-assumption (state-M st)) (state-M st))
              (let ((r (wrap-neg ((z/reify-SM m no_walk?) st))))
                (let ((dd (car r))
                      (ds (cadr r))
                      (R (caddr r))
                      (vs (cadddr r)))
                  (z/global dd)
                  (bind*
                   st
                   (z/local ds R)
                   (lambdag@ (st)
                             (if (and a (check-sat-assuming a (state-M st)))
                                 (begin
                                   (let* ((p (assq a relevant-vars))
                                          (vs^ (cdr p)))
                                     (set! relevant-vars (cons (cons a (append vs vs^)) (remove p relevant-vars)))) 
                                   st)
                                 (if a #f st)))))))))

(define (z/ line)
  (lambdag@ (st)
            (let* ((S (state-S st))
                   (m (remp (lambda (x)
                              (and declares?
                                   (not (var? (cadr (walk* x S)))) ))
                            (list line))))
              ((z/check m #f #f) st))))

(define assumption-count 0)
(define (fresh-assumption)
  (when (and (= (remainder assumption-count gc-assumption-threshold) 0)
             (> assumption-count 0))
    (z/gc!))
  (set! assumption-count (+ assumption-count 1))
  (string->symbol ;(format #f "_a~d" assumption-count)
   (string-append "_a" (number->string assumption-count))
   ))

(define (last-assumption m)
  (let ((r (filter (lambda (x) (and (pair? x)
                                    (eq? 'assert (car x))
                                    (pair? (cadr x))
                                    (eq? (car (cadr x)) '=>)
                                    (equal? (substring (symbol->string (cadr (cadr x))) 0 2) "_a")))
                   m)))
    (if (null? r)
        'true
        (cadr (cadr (car r))))))

(define (wrap-neg e)
  (if (number? e)
      (if (< e 0)
          `(- ,(- e))
          e)
      (if (pair? e)
          (cons (wrap-neg (car e)) (wrap-neg (cdr e)))
          e)))

(define z/assert
  (lambda (e . args)
    (let ((no_walk? (and (not (null? args)) (car args))))
      (lambdag@ (st)
                (let ((a0 (last-assumption (state-M st)))
                      (a1 (fresh-assumption)))
                  (let-values (((rs as) (if (eq? a0 'true)
                                            (values '() '())
                                            (values (cdr (assq a0 relevant-vars))
                                                    (assq a0 assumption-chains)))))
                    (set! relevant-vars (cons (cons a1 rs) relevant-vars))
                    (set! assumption-chains (cons (cons a1 as) assumption-chains))
                    (set! all-assumptions (cons a1 all-assumptions))
                    (bind*
                     st
                     (z/check `((assert (=> ,a1 ,e))
                                (declare-const ,a1 Bool))
                              a1
                              no_walk?)
                     ))
                  )))))

(define relevant-vars '())
(define assumption-chains '())
(define all-assumptions '())
(define (z/reset!)
  (init-log)
  (call-z3 '((reset)))
  (set! decls '())
  (set! relevant-vars '())
  (set! assumption-chains '())
  (set! all-assumptions '())
  (set! assumption-count 0)
  (set! m-subst-map empty-subst-map)
  (set! global-buffer '())
  (set! local-buffer '()))
(define (z/gc!)
  (printf/debug "gc z3...\n")
  (call-z3 '((reset)))
  (call-z3 global-buffer)
  (set! decls '())
  (set! all-assumptions '())
  (set! local-buffer '()))

(define add-model
  (lambda (m)
    (lambdag@ (st)
              (if (null? m)
                  st
                  (bind*
                   st
                   (lambda (st)
                     (let ((var (car (car m)))
                           (val (cadr (car m))))
                       ((== var val) st)))
                   (add-model (cdr m)))))))

(define assert-neg-model
  (lambda (m)
    (let* ([m
            (filter (lambda (x) ; ignoring functions
                      (let ((val (cadr x)))
                        (or (number? val) 
                            (boolean? val)
                            (symbol? val)
                            ))) m)])
      (if (null? m)
          fail
          (z/assert (cadr (neg-model m)))))))

(define z/purge
  (lambdag@ (st)
            (let ((M (state-M st)))
              (if (null? M)
                  st
                  (let ([a (last-assumption (state-M st))])
                    (if (eq? a 'true)
                        st
                        (if (not (check-sat-assuming a (state-M st)))
                            #f
                            (let* ([rs (map (lambda (p)
                                              (cons (reify-v-name (car p)) (car p)))
                                            (cdr (assq a relevant-vars)))]
                                   [rts (map (lambda (x)
                                               (let* ((reified-v (car x)) 
                                                      (v (cdr x))
                                                      (c (lookup-c v st))
                                                      (M (c-M c)))
                                                 (cons reified-v M))) rs)])
                              ((let loop ()
                                 (lambdag@ (st)
                                           (let ((m (get-model-inc)))
                                             (let ((m (map (lambda (x)
                                                             (let ((id (car x))
                                                                   (val (cadr x))
                                                                   (type (caddr x)))
                                                               (let ((p (assq id rs)))
                                                                 (list (cdr p) val type))))
                                                           (filter (lambda (x)
                                                                     (let ((id (car x))
                                                                           (val (cadr x))
                                                                           (type (caddr x)))
                                                                       (let ((p (assq id rts)))
                                                                         (if p (equal? (cdr p) type) #f)))) m))))
                                               (let ((st (state-with-scope st (new-scope))))
                                                 (mplus*
                                                  (bind*
                                                   st
                                                   (add-model m))
                                                  (bind*
                                                   st
                                                   (assert-neg-model m)
                                                   (loop))))))))
                               st)))))))))
