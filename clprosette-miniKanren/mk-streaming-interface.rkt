;;; streaming run and run* interface
;;;
;;; prints the answers as they are generated, along with the current answer count, and total elapsed wall time
;;;
;;; also returns the final answer list, as usual

(define-syntax streaming-run
  (syntax-rules ()
    ((_ n (q) g0 g ...)
     (begin
       (z/reset!)
       (streaming-take n 0 (time-second (current-time))
                       (inc
                        ((fresh (q) g0 g ... z/purge
                                (lambdag@ (st)
                                          (let ((st (state-with-scope st nonlocal-scope)))
                                            (let ((z ((reify q) st)))
                                              (choice z (lambda () (lambda () #f)))))))
                         empty-state)))))
    ((_ n (q0 q1 q ...) g0 g ...)
     (streaming-run n (x)
          (fresh (q0 q1 q ...)
                 g0 g ...
                 (== `(,q0 ,q1 ,q ...) x))))))

(define-syntax streaming-run*
  (syntax-rules ()
    ((_ (q0 q ...) g0 g ...) (streaming-run #f (q0 q ...) g0 g ...))))

(define streaming-take
  (lambda (n answer-count start-time f)
    (cond
      ((and n (zero? n)) '())
      (else
       (case-inf (f)
                 (() '())
                 ((f) (streaming-take n answer-count start-time f))
                 ((c)
                  (let ((total-elapsed-time (- (time-second (current-time)) start-time))
                        (answer-count (add1 answer-count)))
                    (printf "~s [answer ~s, ~s seconds total elapsed (wall time)]\n" c answer-count total-elapsed-time)
                    (cons c '())))
                 ((c f)
                  (let ((total-elapsed-time (- (time-second (current-time)) start-time))
                        (answer-count (add1 answer-count)))
                    (printf "~s [answer ~s, ~s seconds total elapsed (wall time)]\n" c answer-count total-elapsed-time)
                    (cons c (streaming-take (and n (- n 1)) answer-count start-time f)))))))))
