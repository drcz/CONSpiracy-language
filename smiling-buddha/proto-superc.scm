(use-modules (ice-9 pretty-print)) ;; mhm mhm
(add-to-load-path (getcwd)) ;; make geiser happy...
(include-from-path "some-language-stuff.scm")

;;;; simplifier ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (contains-jokers? expr)
  (match expr
    ['&JOKER #t]
    [(x . xs) (or (contains-jokers? x) (contains-jokers? xs))]
    [_ #f]))
(e.g. (contains-jokers? '(2 . &JOKER)))
(e.g. (not (contains-jokers? '(2 . 3))))

(define (un-lifted expr)
  (match expr
    [(? constant? c) c]
    [e `(quote ,e)]))

(define (simplified expr #;wrt metabinding)
  (let simp ((expr expr))
    (match expr
      [(? constant? c) c]
      [(? variable? v)
       (let ([val (lookedup v metabinding)])
	 (if (contains-jokers? val) v (un-lifted val)))]
      [('quote _) expr]
      [('quasiquote qq) (match (simplest-qq (map-unquote simp qq))
			  [('unquote e) e]
			  [(? constant? c) c]
			  [e `(,'quasiquote ,e)])]
      [('if p c a) (match (simp p)
		     [#f (simp a)]
		     [#t (simp c)]
		     [('quote #f) (simp a)]
		     [('quasiquote #f) (simp a)]
		     [('quote _) (simp c)]
		     [sp `(if ,sp ,(simp c) ,(simp a))])]
      [((? primop-symbol? p) . args) (simplified-primapp `(,p . ,(map simp args)))]
      [('APPLY (? primop-symbol? p) . args) (simp `(,p . ,args))]
      [('APPLY . stuff) `(APPLY . ,(map simp stuff))])))

(define (simplified-primapp ap) ;; this one can be quite incorrect...
  (match ap
    [('= x x) #t]
    [('= (? constant?) (? constant?)) #f]
    [('+ (? numeral? n) (? numeral? m)) (+ n m)]
    [('+ 0 x) x]
    [('+ x 0) x]
    [('+ x x) `(* 2 ,x)]
    [('- (? numeral? n) (? numeral? m)) (- n m)]
    [('- x 0) x]
    [('- x x) 0]
    [('* (? numeral? n) (? numeral? m)) (* n m)]
    [('* 0 x) 0]
    [('* x 0) 0]
    [('* 1 x) x]
    [('* x 1) x]
    [('truth-value? (? truth-value?)) #t]
    [('truth-value? (? numeral?)) #f]
    [('atom? ('quote (? pair?))) #f]
    #;...
    [('numeral? (? numeral?)) #t]
    [('numeral? (? constant?)) #f]
    [('numeral? ('quote _)) #f]
    #;...
    [something something]))

(e.g. (simplified '(APPLY + 2 3) '()) ===> 5) ;; fajnie, nie?
(e.g. (simplified '(APPLY * 0 x) '([x . x])) ===> 0)
(e.g. (simplified '(APPLY * x x) '([x . x])) ===> (* x x))
(e.g. (simplified '(if (= x y) `(,x) `(x ,x y ,y)) '([x . 3] [y . 1]))
      ===> `(x 3 y 1))
(e.g. (simplified '(if (= x y) `(,x) `(x ,x y ,y)) '([x . 3] [y . 3]))
      ===> `(3))
(e.g. (simplified '(if (= x y) `(,x) `(x ,x y ,y)) '([x . &JOKER] [y . 1]))
      ===> (if (= x 1) `(,x) `(x ,x y 1)))


;;;; meta-matcher ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (matching #;for meta-expression #;against pattern)
  (let binding ([mexpr meta-expression]
		[patt pattern]
		[result '()])
    (match patt
      ['_ result]      
      [(? constant? c) (and (or (eq? mexpr '&JOKER) (equal? c mexpr)) result)]
      [('quote e) (and (or (eq? mexpr '&JOKER) (equal? e mexpr)) result)]
      [(? variable? v)
       (let ([val (lookedup v result)])
	 (cond [(eq? val '&UNBOUND) (updated result v mexpr)]
	       [(eq? val '&JOKER) (updated result v mexpr)]
	       [(or (eq? mexpr '&JOKER) (equal? val mexpr)) result]
	       [else #f]))]
      [(p . ps) (and-let* ([(e . es) (if (eq? '&JOKER mexpr)
					 '(&JOKER . &JOKER)
					 mexpr)]
			   [result0 (binding e p result)])
		  (binding es ps result0))]
      [otherwise `ERROR-SKURWESYN])))

(e.g. (matching '(2 3 4) '(x y z)) ===> ((z . 4) (y . 3) (x . 2)))
(e.g. (matching '(2 3 2) '(x y x)) ===> ((y . 3) (x . 2)))
(e.g. (matching '(2 3 3) '(x y x)) ===> #f)
(e.g. (matching '(2 &JOKER &JOKER) '(x y x)) ===> ((y . &JOKER) (x . 2)))
(e.g. (matching '(&JOKER &JOKER 2) '(x y x)) ===> ((x . 2) (y . &JOKER)))
(e.g. (matching '((2 . &JOKER)) '(a)) ===> ((a . (2 . &JOKER))))
(e.g. (matching '(23 &JOKER) '(n (x . xs))) ===> ((xs . &JOKER) (x . &JOKER) (n . 23)))

;;;; now finding out node's children... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (all-applications #;in expr)
  (match expr ;; mind the oder in the first clause -- outer appl is the last one!
    [('APPLY . as) (fold-right append `(,expr) (map all-applications as))]
    [('quasiquote qq) (append-map-unquote all-applications qq)]
    [('if p c a) (append (all-applications p)
			 (all-applications c)
			 (all-applications a))]
    [((? primop-symbol?) . as) (append-map all-applications as)]
    [_ '()]))

(e.g. (all-applications '(APPLY (APPLY `(0) x (APPLY z y))
				23
				(+ x y)
				(APPLY `(1) x)))
      ===> [(APPLY z y) ;; see? innermost == first (``applicative order'')
	    (APPLY (quasiquote (0)) x (APPLY z y))
	    (APPLY (quasiquote (1)) x)
	    (APPLY (APPLY (quasiquote (0)) x (APPLY z y))
		   23
		   (+ x y)
		   (APPLY (quasiquote (1)) x))])


(define (pp<-application (fn . as) metabinding)
  (define (metaexpression #;from e)
    "approximation of information on e wrt metabinding"
    (match e
      [(? constant? c) c]
      [(? variable? v) (lookedup v metabinding)]
      [('quote e) e]
      [('quasiquote qq) (let mp-unq ((qq qq))
			  (match qq
			    [('unquote e) (metaexpression e)]
			    [(h . t) `(,(mp-unq h) . ,(mp-unq t))]
			    [e e]))]
      [otherwise '&JOKER]))
  `(,fn . ,(map metaexpression as)))

(e.g.
 (pp<-application
  '(APPLY `(&CLOSURE 0 ,y) x (APPLY z y))
  '([x . (2 . &JOKER)] [y . (3 6 . &JOKER)] [z . (&CLOSURE 3)]))
 ===> (APPLY (&CLOSURE 0 (3 6 . &JOKER)) (2 . &JOKER) &JOKER))

;;; now we get pretty sketchy...


(define example1
  '(def APPLY
	(bind (('&CLOSURE 0) xs) (APPLY `(&CLOSURE 4) (APPLY `(&CLOSURE 2) 3) xs)
	      (('&CLOSURE 1) op e ()) e
	      (('&CLOSURE 1) op e (x . xs)) (APPLY op x (APPLY `(&CLOSURE 1) op e xs))
	      (('&CLOSURE 2) x) `(&CLOSURE 3 ,x)
	      (('&CLOSURE 3 x) y) (APPLY '+ x y)
	      (('&CLOSURE 4) f xs) (APPLY `(&CLOSURE 1) `(&CLOSURE 5 ,f) () xs)
	      (('&CLOSURE 5 f) h t) `(,(APPLY f h) unquote t)
	      ;;; + satan's little helpers:
	      ('+ n m) (+ n m)
	      ('- n m) (- n m)
	      ('* n m) (* n m)
	      ('= n m) (= n m)
	      ('atom? x) (atom? x)
	      ('numeral? x) (numeral? x)
	      ('bind-form? ((quote &CLOSURE) . _)) #t
	      ('bind-form? _) #f
	      ('truth-value? x) (truth-value? x))))
  
;;; so atm we assume a program is only 1 def...
(define (possible-clauses #;consistent-with pp #;in program)
  (and-let* ([('APPLY . args) pp]
	     [('def 'APPLY ('bind . clauses)) program])
    (let p-c ([clauses clauses])
      (match clauses
	[() '()]
	[(pat body . clauses*) #;[pretty-print `(,pat ,(matching args pat))]
	 (match (matching args pat)
				 [#f (p-c clauses*)]
				 [binding `(,pat ,(simplified body binding)
					    . ,(p-c clauses*))])]))))

(e.g.
 (possible-clauses '(APPLY (&CLOSURE 1) (&CLOSURE 2) () &JOKER) example1)
 ===>
 [(('&CLOSURE 1) op e ()) ()
  (('&CLOSURE 1) op e (x . xs))  (APPLY '(&CLOSURE 2)
					x
					(APPLY `(&CLOSURE 1)
					       '(&CLOSURE 2)
					       ()
					       xs))])
 
;;; -- a whistle for applications [ignoring that first argument is numeral?]
;;; -- building and re-building the process tree using the above...
;;; (...)

