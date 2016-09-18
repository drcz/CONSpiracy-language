#!/usr/bin/guile -s
!#

;;; scraps of what will be the final CONSpiracy->DRC->C/js/pyth/?
;;; last significant touch 2016-09-18, drcz
(use-modules (srfi srfi-1) (ice-9 nice-9) (ice-9 pretty-print))

;;; todo: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; -- unit tests for every fragment,
;;; -- fix d17n bugs
;;; -- implement DRC machine in CONSpiracy
;;; -- implement [+ modify proof of validity] CONS1->DRC compiler
;;; -- ... [[a lot of stuff]]

(define (lookup s env) (assoc-ref env s))
(define (insert s v env) `((,s . ,v) . ,env))
(define (update s v env) (insert s v (alist-delete s env)))

(define (numeral? n) (number? n))
(define (primitive? p) (procedure? p))
(define (truth-value? c) (boolean? c))
(define (bind-form? b) (and-let* ((('&bind _ _) b))))
(define (constant? c) (or (null? c)
			  (numeral? c)
			  (string? c)
			  (primitive? c) #;(primitive? c)
			  (truth-value? c)
			  (bind-form? c)))

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

(define (and->ifs es) (fold-right (lambda (h t) `(if ,h ,t ())) 'T es))
(define (or->ifs es)  (fold-right (lambda (h t) `(if ,h T ,t)) '() es))
(define (not->if e) `(if ,e () T))

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
    [('bind 'args body) `(bind args ,(compile body))]
    [('bind (v) body) `(bind (,v) ,(compile body))]    
    [('bind . cases) (compile (bind-form->code expr))]
    [(rator . (? variable? v)) `(,(compile rator) . ,v)]
    [(rator . rands) (map compile expr)]))

;;; todo: lambda co nie używa / let co nie używa?
;;; todo: sprytniejsze bind-form->code :)


#;[pretty-print
 (compile '(bind (f ()) () (f (x . xs)) `(,(f x) . ,(map f xs)))) ]

;[pretty-print (compile '(let ((a 2) (b 3) (c (+ a b))) (* c c)))]


;;; Y-inlining, i.e. ... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ...........................................................
;;; ... the Holy Name, ...........................................
;;; ... which stands for itself and as such can perform miracles ....
;;; ....................................................................

(define (bound-vars #;of pattern)
  (delete-duplicates
   (let vars-of ((pattern pattern))
     (match pattern
       [(? constant? c) '()]
       [('quote _) '()]
       [(? variable? v) `(,v)]
       [('? pred v) `(,v)]
       [('? pred) '()]
       ['_ '()]
       [(p . ps) (append (vars-of p) (vars-of ps))]))))
;(bound-vars '('if (= x y) a y))

(define (free-vars #;of expr)
  (delete-duplicates
   (let vars-of ((expr expr))
     (match expr
       [(? constant? c) '()]
       [(? variable? v) `(,v)]
       [('lambda vs e) (lset-difference eq? (free-vars e) vs)] ;; :D
       [('bind . cases) (let vars-of-cases ((cases cases))
			  (match cases
			    [() '()]
			    [(p b . rest) (append (lset-difference
						   eq?
						   (delete-duplicates (vars-of b))
						   (bound-vars p))
						  (vars-of-cases rest))]))]
       [('let bindings e) (vars-of (let->lambda bindings e))]
       [('if pre con alt) (append (vars-of pre)
				  (vars-of con)
				  (vars-of alt))]
       [('and . rands) (append-map vars-of expr)]
       [('or . rands) (append-map vars-of expr)]
       [('not e) (vars-of e)]        
       [('quote _) '()]
       [('quasiquote e) (let qq-vars-of ((exp e))
			  (match exp
			    [('unquote e) (vars-of e)]
			    [(h . t) (append (qq-vars-of h) (qq-vars-of t))]
			    [e '()]))]
       [('Y b) (free-vars b)]
       [(rator . (? variable? v)) `(,v . ,(vars-of rator))]
       [(rator . rands) (append-map vars-of expr)]))))

#;(e.g. (free-vars '(+ (* x x) y)) ===> '(x y))

;(lset-difference eq? '(x x q w e q) '(q e))
(free-vars '((Y (bind (apd)
		      (bind (() ys) ys
			    ((x . xs) ys) `(,x #;,a . ,(apd xs ys)))))
	     x (rev y)))

;;; Tada-da-DAAAMmm
(define (program->Name main-expression program)
  (let find-name ((expr main-expression)
		  (bound '()))
    (match expr
      [(? constant? c) c]
      [(? variable? v) (if (or (member v bound)
			       (not (lookup v program)))
			   v
			   (let ((expr (lookup v program)))
			     (find-name (if (member v (free-vars expr))
					    `(Y (bind (,v) ,expr))
					    expr)
					bound)))]
      [('quote _) expr]
      [('Y e) `(Y ,(find-name e bound))]
      [('bind . cases) `(bind . ,(let f-n-cases ((cases cases))
				   (match cases
				     [()
				      '()]
				     [(p b . rest)
				      `(,p ,(find-name b
						       (delete-duplicates ; :P
							(append (bound-vars p)
								bound)))
					   . ,(f-n-cases rest))])))]
      [('if p c a) `(if ,(find-name p bound)
			,(find-name c bound)
			,(find-name a bound))]
      [('and . es) `(and . ,(map (lambda (e) (find-name e bound)) es))]
      [('or . es) `(or . ,(map (lambda (e) (find-name e bound)) es))]
      [('not e) `(not ,(find-name e bound))]
      [(rator . rands) `(,(find-name rator bound)
			 . ,(map (lambda (e) (find-name e bound)) rands))]
      [(rator . (? variable? v)) `(,(find-name rator bound)
				   . ,(find-name v bound))])))

#;[begin  
  (pretty-print
   (program->Name '(f (g x))
		  '[(f . (bind (x) (x x)))
		    (g . (bind (x) (if (= x 0) () `(,(g (- x 1))))))]))
  
  (pretty-print
   (program->Name '(g (f x))
		  '[(f . (bind (x) (x x)))
		    (g . (bind (x) (if (= x 0) () `(,(g (- x 1))))))]))
  
  (pretty-print
   (program->Name '(foldr apd () (map f xs))
		  '[(foldr . (bind (_ e ()) e
				   (op e (x . xs)) (op x (foldr op e xs))))
		    (cons . (bind (h t) `(,h . ,t)))
		    (apd . (bind (xs ys) (foldr cons ys xs)))
		    (map . (bind (f xs) (foldr (bind (h t) `(,(f h) . ,t))
					       ()
					       xs)))
		    (f . (bind (xs) (map (bind (x) (* x x)) xs)))
		    (xs . '((1 2) (2 3) (3 4)))])) ;;; wow!
] 
  

;;; CONS2 defunctionalization ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (all-lambdas #;of expr)
  (delete-duplicates
   (let lambdas-of ((expr expr))
     (match expr
       [('lambda a b) `(,expr . ,(lambdas-of b))]
       [('if pre con alt) (append (lambdas-of pre)
				  (lambdas-of pre)
				  (lambdas-of pre))]
       [(h . t) (append (lambdas-of h) (lambdas-of t))]
       [e '()]))
   equal?))

;(all-lambdas '((lambda (x) (* x x)) (+ 2 ((lambda (x) (+ x 3)) 0))))

(define (mk-apply lambdas/free-vars labels)
  (fold-right  (lambda (((symbol . fvals) . (('lambda as b) . fvars)) rest)
		 `(if (= (car label) (quote ,symbol))
		      (let ,(append (map list fvars fvals)
				    (let aas ((as as)
					      (tgt 'args))
				      (match as
					[() '()]
					[(a . as) `((,a (car ,tgt))
						    . ,(aas as `(cdr ,tgt)))])))
			,b)
		      ,rest))
	       ''MISMATCH!
	       (map cons labels lambdas/free-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;; !! do not use the one below for now:
(define (d17n expr)  
  (let-rec ((d18 (lambda (expr)
;		(pretty-print `(d18 ,expr)) ;;;;;;;;
		   (match expr
		     [(? constant? c) c]
		  [(or 'car 'cdr 'cons) expr] ;>
		  [(? variable? v) v]
		  [('quote _) expr]
#;		  [('quasiquote e) `(quasiquote ,(let qq-d18 ((e e))
						   (match e
						     [(unquote e) `(unquote ,(d18 e))]
						     [(h . t) `(,(qq-d18 h) . ,(qq-d18 t))]
						     [(e e)])))]
		  [('if pre con alt) `(if ,(d18 pre) ,(d18 con) ,(d18 alt))]
		  [(('lambda as b) . es) `(APPLY ,(lambda->label `(lambda ,as ,b))
					    ,(map d18 es))]
		  [('lambda as b) (lambda->label `(lambda ,as ,b))]
		  [('car e) `(car ,(d18 e))] ;|
		  [('cdr e) `(cdr ,(d18 e))] ;)
		  [('cons e1 e2) `(cons ,(d18 e1) ,(d18 e2))] ;D
		  [((? primitive? p) . es) `(,p . ,(map d18 es))] ;]
		  [((? variable? v) . es) `(APPLY ,v ,(map d18 es))]
		  [(h . t) `(,(d18 h) . ,(d18 t))])))		
	    (lambdas (all-lambdas #;of expr))
	    (lambdas-d (map d18 lambdas)) ;; ?!
	    ;(_elo_ (pretty-print lambdas)) ;;;;;;;;;;;;;
	    (lambdas/free-vars (map (lambda (l) `(,l ,(free-vars l))) lambdas-d))
	    ;(_elo_ (pretty-print lambdas/free-vars)) ;;;;;;;;
	    (l->l-map (map (lambda (l (l-d fvars)) `(,l . (,(gensym "L") . ,fvars)))
			   lambdas
			   lambdas/free-vars))
	    ;(_elo_ (pretty-print l->l-map)) ;;;;;;;;;;;;
	    (lambda->label (lambda (l) (lookup l l->l-map)))
	    (apply-body (mk-apply lambdas/free-vars (map lambda->label lambdas))))
	   (d18 expr)))

;;;;;;;; ?!?!

;(pretty-print (d17n '((lambda (x) (* x x)) (+ 2 3))))

(pretty-print
 (d17n '(((lambda (x) (lambda (y) (+ x y))) 2) 3)))

;;; something is wrong here...
;; tbc
