#!/usr/bin/guile -s
!#
;;; scraps of what will be the final CONSpiracy->DRC->C/js/pyth/? <- yeah, sure
;;; last significant touch 2016-09-18, drcz

;;; 2016-12-26 added "main" so that it read program from stdout, and removed the crap.
(use-modules (srfi srfi-1) (ice-9 nice-9) (ice-9 pretty-print))

;;; todo: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; -- unit tests for every fragment,
;;; -- smarter treatment of pattern-matching (moving common tests outwards...)
;;; ...
;;; nb for now we ignored the string-ops...

(define (lookup s env) (assoc-ref env s))
(define (insert s v env) `((,s . ,v) . ,env))
(define (update s v env) (insert s v (alist-delete s env)))

(define (numeral? n) (number? n))
(define (primitive? p) (member p
			       '(+ - * / = < %
				  ; ++ string-length substring
				   atom? #;string? truth-value? numeral?))
  #;(procedure? p))
(define (truth-value? c) (boolean? c))
(define (bind-form? b) (and-let* ((('&bind _ _) b))))
(define (constant? c) (or (null? c)
			  (numeral? c)
			  (string? c)
			  (primitive? c)
			  (truth-value? c)
			  (bind-form? c)))
(define (atom? x) (not (pair? x))) ; ?
(define (variable? v) (and (symbol? v) (not (constant? v)))) ; :)

(define (pattern->conditions.binding pattern)
  (let* (((code . binding) 
	  (let p->c ((pattern pattern)
		     (formal-name 'args)
		     (binding '()))
	    (match pattern
	      [() `[((= ,formal-name ())) . ,binding]]
	      [(? number? n) `[((= ,formal-name ,n)) . ,binding]]
	      [('quote e) `[((= ,formal-name (quote ,e))) . ,binding]]
	      [('? guard) `[((,guard ,formal-name)) . ,binding]]
	      [('? guard (? variable? v)) `[((,guard ,formal-name))
					    . ((,v . ,formal-name) . ,binding)]]
	      [(? variable? v) (let* ((val (lookup v binding)))
				 (if val
				     `[((= ,formal-name ,val)) . ,binding]
				     `[() . ((,v . ,formal-name) . ,binding)]))]
	      [(h . t) (let* (((code-h . binding0)
			       (p->c h `(car ,formal-name) binding))
			      ((code-t . binding1)
			       (p->c t `(cdr ,formal-name) binding0)))
			 `[,(append `((pair? ,formal-name)) code-h code-t)
			   . ,binding1])]))))
    `(,code ,binding)))

#;[begin ;; e.g.
  (pretty-print (pattern->conditions.binding '(x y x 6)))
  (pretty-print (pattern->conditions.binding '(x . x)))
  (pretty-print (pattern->conditions.binding '('if ('= (? num? n1) n1) a 23)))
  (pretty-print (pattern->conditions.binding '('if ('= y x) 6 9)))]


(define (bind-form->code form)
  (match form
    [('bind . something)
     `(bind args ,(bind-form->code something))]
    [(pattern body . rest)
     (let* (((conditions binding)
	     (pattern->conditions.binding pattern)))
       `(if ,(if (> (length conditions) 1)
		 `(and . ,conditions)
		 (first conditions))
	    ,(if (> (length binding) 0)
		 `(let ,(map (lambda ((v . e)) `(,v ,e))
			     binding)
		    ,body)
		 body)
	    ,(bind-form->code rest)))]
    [() '(quote MISMATCH!)]))

#;[begin ;; e.g.
  (pretty-print
   (bind-form->code '(bind (0) 1
			   (1) 1
			   (2) 2
			   (n) (* n (f (- n 1))))))

  (pretty-print
   (bind-form->code '(bind (f ()) ()
			   (f (x . xs)) (cons (f x) (map f xs)))))

  (pretty-print
   (bind-form->code '(bind (('+ a b)) (+ a b)
			   (('* a b)) (* a b)
			   (('- a b)) (- a b))))
  
  (pretty-print
   (pattern->conditions.binding '(('+ a b))))]

;;; boolean connectors -> ifs... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (and->ifs es) (fold-right (lambda (h t) `(if ,h ,t #f)) #t es))
(define (or->ifs es)  (fold-right (lambda (h t) `(if ,h #t ,t)) #f es))
(define (not->if e) `(if ,e #f #t))

;;; and something for the quasiquotes... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (quasiquote->cons qq)
  (match qq
    [('unquote e) e]
    [(h . t) `(cons ,(quasiquote->cons h) ,(quasiquote->cons t))]
    [e `(quote ,e)]))

;;; and let->lambda thing... (this is like let*) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (let->lambda binding body)
  (let l->l ((binding binding))
    (match binding
      [() body]
      [((v e) . rest) `((bind (,v) ,(l->l rest)) ,e)])))
;(let->lambda '((x 2) (y 3)) '(+ x y))


;;; and now...
;;; Taadaaam!!!
;;; THE COMPILER ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (compile expr)
  (match expr
    [(? constant? c) c]
    [(? variable? v) v]
    [('quote e) expr]
    [('quasiquote e) (compile (quasiquote->cons e))]
;    [('cons h t) `(cons ,(compile h) ,(compile t))]
    [('and . es) (compile (and->ifs es))]
    [('or . es) (compile (or->ifs es))]
    [('not e) (compile (not->if e))]
    [('if p 'T ()) (compile p)]
    [('if p p ()) (compile p)]
    [('if p c a) `(if ,(compile p) ,(compile c) ,(compile a))]
    [('let bndg e) (compile (let->lambda bndg e))]
    [('bind 'args body) `(lambda args ,(compile body))]
    [('bind (v) body) `(lambda (,v) ,(compile body))]
    [('lambda a b) `(lambda ,a ,(compile b))]
    [('bind . cases) (compile (bind-form->code expr))]
    [(rator . (? variable? v)) `(,(compile rator) . ,v)]
    [(rator . rands) (map compile expr)]))


;;; just a fast treatment for a program consisting of a list of definitions
;;; followed by a single expression...
(let* ((program (reverse (read)))
       (defs (reverse (cdr program))) ;; :D
       (defs (cons `(def pair? (bind (x) (not (atom? x)))) defs)) ;; :>
       (main (car program))
       (new-program `[,(compile main)
		      . ,(map (lambda ((_ s e)) `(,s . ,(compile e))) defs)]))
  (pretty-print new-program))

#;[pretty-print
 (compile '(bind (f ()) () (f (x . xs)) `(,(f x) . ,(map f xs)))) ]
;[pretty-print (compile '(let ((a 2) (b 3) (c (+ a b))) (* c c)))]

