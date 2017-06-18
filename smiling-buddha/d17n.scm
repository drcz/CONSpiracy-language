(use-modules (ice-9 pretty-print)) ;; only for testing...
(add-to-load-path (getcwd)) ;; make geiser happy...
(include-from-path "some-language-stuff.scm")

;;; as the name suggests, this is [our second] defunctionalizer;
;;; this time working with pattern-matching so that the output is
;;; at least party readable.
;;; this is dirty, incomplete and buggy prototype, BUT it should suffice
;;; to check out some new ideas. 

;;; an example CONSpiracy code with some HOFs:
(define example1
  '[ (def run-me (bind (xs) (map (mk-add 3) xs)))
     (def foldr (bind (op e ()) e
		      (op e (x . xs)) (op x (foldr op e xs))))
     (def mk-add (bind (x) (bind (y) (+ x y))))
     (def map (bind (f xs) (foldr (bind (h t) `(,(f h) . ,t)) () xs)))])
;;; the goal is to convert it into first-order CONSpiracy...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (map-append-every-second f xs) ;; mooooooom...?! 
  (match xs
    [() '()] ;; on the other hand, this is a very specific generalization, right?
    [(x y . xs) (append (f y) (map-append-every-second f xs))]))

(define (all-bind-forms #;in expr) ;; TODO replace with ``general collector''
  (match expr
    [(? constant?) '()]
    [(? variable?) '()]
    [('quote _) '()]
    [('quasiquote qq) (append-map-unquote all-bind-forms qq)]
    [('bind . cases) `(,expr . ,(map-append-every-second all-bind-forms cases))]
    [('if p c a) (append (all-bind-forms p)
			 (all-bind-forms c)
			 (all-bind-forms a))]
    [(f . (? variable?)) (all-bind-forms f)]
    [(f . as) (append-map all-bind-forms expr)]))

(e.g. (all-bind-forms example1) ===>
      [(bind (xs) (map (mk-add 3) xs))
       (bind (op e ()) e (op e (x . xs)) (op x (foldr op e xs)))
       (bind (x) (bind (y) (+ x y)))
       (bind (y) (+ x y))
       (bind (f xs) (foldr (bind (h t) (quasiquote ((unquote (f h)) unquote t))) () xs))
       (bind (h t) (quasiquote ((unquote (f h)) unquote t)))])

(define (vars-bound #;by pattern)
  (match pattern
    [() '()]
    [(? constant?) '()]
    [('quote _) '()]
    ['_ '()]
    [(? variable? v) `(,v)]
    [(p . ps) (append (vars-bound p) (vars-bound ps))]))


;;; mind this one does include topenv ones as technically they are free in
;;; each expression...
(define (free-variables #;of expr)
  (delete-duplicates
   (let FV ((expr expr))
     (match expr
       [(? constant?) '()]
       [(? variable? v) `(,v)]
       [('quote _) '()]
       [('quasiquote qq) (append-map-unquote FV qq)]
       [('bind . cases)
	(let magick ((cases cases))
	  (match cases
	    [() '()]
	    [(pat expr . cases) (append (difference (FV expr) (vars-bound pat))
					(magick cases))]))]
       [('if p c a) (append (FV p) (FV c) (FV a))]
       [(f . (? variable? v)) `(,v . ,(FV f))]
       [(f . as) (append-map FV expr)]))))

(e.g. (free-variables '(quasiquote ((unquote x) . (unquote (apd xs ys)))))
      ===> (x apd xs ys))

;;; TODO: revert this arrow ; add better name ; catalogue?
(define (bindform->constructor #;in expr #;wrt bindforms-catalogue)
  (let bf->c ((expr expr))
    (match expr
      [(? constant?) expr]
      [(? variable?) expr]
      [('quote _) expr]
      [('quasiquote qq) `(,'quasiquote ,(map-unquote bf->c qq))]
      [('bind . _) (lookedup expr bindforms-catalogue)]
      [('if p c a) `(if ,(bf->c p) ,(bf->c c) ,(bf->c a))]
      ;;; now one small cheat -- we will also annotate applications.
      ;;; perhaps this should happen in separate step, or even better this
      ;;; function should have a nicer name but FUCK YOU -- it's a prototype!
      [(f . (? variable? v)) `(APPLY ,(bf->c f) . ,v)] ;; ?!
      [((? primop-symbol? f) . as) `(APPLY ',f . ,(map bf->c as))]
      [(f . as) `(APPLY . ,(map bf->c expr))])))


;;; two completely mindless defs hehehe.
(define (patternized constructor)
  (and-let* ([(_qqt (&CLOSURE id . vars)) constructor]
	     [patternized-vars (map (lambda ((_unquote var)) var) vars)])
    `(&CLOSURE ,id . ,patternized-vars)))

(define (with-inlined-topenv #;of program #;the expr)
  (let ((defs (map (lambda ((_df v e)) `(,v . ,e)) program)))
    (let inline ((expr expr))
      (match expr
	[(? constant?) expr]
	[(? variable? v) (match (lookedup v defs) ['&UNBOUND v] [e e])]
	[('quote _) expr]
	[('quasiquote qq)
	 `(,'quasiquote
	   ,(map-unquote inline qq))]
	[('bind . _) `THERE-ARE-NO-BINDS] ;;; he_he
	[('if p c a) `(if ,(inline p) ,(inline c) ,(inline a))]
	[('APPLY f . (? variable? v)) `(APPLY ,(inline f) . ,(inline v))]
	[('APPLY f . as) `(APPLY . ,(map inline `(,f . ,as)))])))) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; now the heart y'know...

;;; below by program we mean a list of definitions as example1.
;;; technically there should be also some initial application; we can
;;; assume [again] it is the first definition [i.e. "first bind form in code"]
;;; called with program's inputs as arguments...

(define (defunctionalized program) ;; RZYGI!!! / not too fancy
  (let* ([topenv-vars
	  (map (lambda ((_ name expr)) name) program)]
	 [bindforms
	  (append-map (lambda ((_ name expr)) (all-bind-forms expr)) program)]
	 [bindforms-catalogue
	  (map (lambda (bf index)
		 (let* ([closure-vars
			 (difference (free-variables bf) topenv-vars)]
			[constructor
			 `(,'quasiquote (&CLOSURE ,index 
					 . ,(map (lambda (v) `(,'unquote ,v))
						 closure-vars)))])
		   `(,bf . ,constructor)))
	       bindforms
	       (iota (length bindforms)))]
	 [new-program
	  (map (lambda ((df name expr))
		 `(,df ,name ,(bindform->constructor expr bindforms-catalogue)))
	       program)]
	 [APPLY-clauses
	  (append-map (lambda (((_bind . cases) . cnstr))
			(let dissect ([cases cases])			  
			  (match cases
			    [() '()]
			    [(ptrn body . cases)
			     (let* ([new-ptrn `(,(patternized cnstr) . ,ptrn)]
				    [new-body
				     (with-inlined-topenv new-program
							  (bindform->constructor
							   body
							   bindforms-catalogue))])
			     `(,new-ptrn ,new-body . ,(dissect cases)))])))
		      bindforms-catalogue)]
	 [primop-clauses ;; some shit to allow using primop-symbols as args...
	  '(('+ n m) (+ n m)
	    ('- n m) (- n m)
	    ('* n m) (* n m)
	    ('= n m) (= n m) ;; "(= n n) #t (= n m) #f" might inline harder...
	    ('atom? x) (atom? x)
	    ('numeral? x) (numeral? x)
	    ('bind-form? ('&CLOSURE . _)) #t
	    ('bind-form? _) #f
	    ('truth-value? x) (truth-value? x))]
	 #;...)
    `(def APPLY (bind ,@APPLY-clauses ,@primop-clauses))))


;;; nevertheless THIS IS FUCKIN' MAGICK
[e.g.
 (defunctionalized #;example1 ;; <- easier to read with ex1 inlined here:
   '[ (def run-me (bind (xs) (map (mk-add 3) xs)))
      (def foldr (bind (op e ()) e
		       (op e (x . xs)) (op x (foldr op e xs))))
      (def mk-add (bind (x) (bind (y) (+ x y))))
      (def map (bind (f xs) (foldr (bind (h t) `(,(f h) . ,t)) () xs)))])
 ===>
 (def APPLY
      (bind ((&CLOSURE 0) xs) (APPLY `(&CLOSURE 4) (APPLY `(&CLOSURE 2) 3) xs)
	    ((&CLOSURE 1) op e ()) e
	    ((&CLOSURE 1) op e (x . xs)) (APPLY op x (APPLY `(&CLOSURE 1) op e xs))
	    ((&CLOSURE 2) x) `(&CLOSURE 3 ,x)
	    ((&CLOSURE 3 x) y) (APPLY '+ x y)
	    ((&CLOSURE 4) f xs) (APPLY `(&CLOSURE 1) `(&CLOSURE 5 ,f) () xs)
	    ((&CLOSURE 5 f) h t) `(,(APPLY f h) unquote t)
	    ;;; + satan's little helpers:
	    ('+ n m) (+ n m)
	    ('- n m) (- n m)
	    ('* n m) (* n m)
	    ('= n m) (= n m)
	    ('atom? x) (atom? x)
	    ('numeral? x) (numeral? x)
	    ('bind-form? ((quote &CLOSURE) . _)) #t
	    ('bind-form? _) #f
	    ('truth-value? x) (truth-value? x)))]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#;(pretty-print 
(defunctionalized
   '[ (def apd (bind (() ys) ys
		     ((x . xs) ys) `(,x . ,(apd xs ys))))
      (def prsty (bind (as) (apd '(q w) as))) 
      (def trdny (bind (as) (apd as '(q w)))) ]) )

#;(pretty-print
 (defunctionalized
   '( (def pow (bind (m 0) 1
		     (m n) (* m (pow m (- n 1)))))
      (def prst (bind (m) (pow m 2)))
      (def trdn (bind (n) (pow 2 n))) )) )

#;(pretty-print
 (defunctionalized '((def dupsztyl (bind (f) (bind-form? f)))
		     (def djag (bind () (dupsztyl dupsztyl))))))
"
(def APPLY
     (bind ((&CLOSURE 0) f) (APPLY 'bind-form? f)
           ((&CLOSURE 1)) (APPLY `(&CLOSURE 0) `(&CLOSURE 0))
	    ;;; + satan's little helpers:
	    ('+ n m) (+ n m)
	    ('- n m) (- n m)
	    ('* n m) (* n m)
	    ('= n m) (= n m)
	    ('atom? x) (atom? x)
	    ('numeral? x) (numeral? x)
	    ('bind-form? ((quote &CLOSURE) . _)) #t
	    ('bind-form? _) #f
	    ('truth-value? x) (truth-value? x)))

(APPLY '(&CLOSURE 1))
"
;;; gites.
