#!/usr/bin/guile -s
!# ;; CONSpiracy v 0.1 REPL by drcz, last touch 2016-09-18, Eindhoven ;;
(include "CONSpiracy-implementation.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the second-best unit-test "library" in the world: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-macro (assert p)
  `(if ,p
       #t
       (begin (display '(assertion ,p failed!))
              (newline)
              #f)))

(define-macro (assert-eq? p v)
  `(if (equal? ,p ,v)
       #t
       (begin (pretty-print (list 'assert-eq? ',p ,v 'failed!))
              (pretty-print (list 'because ',p '=> ,p))
              (newline)
              #f)))
;;; eg:
;(assert (= 2 2))
;(assert-eq? (+ 3 3) (* 3 2))
;;; failed test pretty-prints what went wrong, eg
;(assert (= 2 3))
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test-eval)
  (and [assert-eq? (Eval '23 '() '()) 23]
       [assert-eq? (Eval '(+ 2 3) '() *initial-env*) 5]
       [assert-eq? (Eval '(+ (* 7 8) x) '((x . 13)) *initial-env*) 69]
       [assert (Eval '(= x 2) '((x . 2)) *initial-env*)]
       [assert (not (Eval '(= x 2) '((x . 3)) *initial-env*))]
       (let* ((map-def
	       '(Y (bind (map)
			 (bind (_ ())
			       ()
			       (f (x . xs))
			       (quasiquote ((unqote (f x))
					    . (unqote (map f xs))))))))
	      (sq-def '(bind (x) (* x x)))
	      (defs (append *initial-env* `((map
					     . ,(Eval map-def '() *initial-env*))
					    (sq
					     . ,(Eval sq-def '() *initial-env*)))))
	      (expr '(map sq (quasiquote (1 2 3 (unqote x))))) ;; !
	      (val (Eval expr '((x . 4)) defs)))
	 [assert-eq? val '(1 4 9 16)])
       ;; ...
       '(ALL GOOD -- keep going!))) ; ?
       
;;;;;;;;;; cuś się zjebało -- TODO
;;; ...

[and (test-eval)
     ;; ...
     ]

;;; .
