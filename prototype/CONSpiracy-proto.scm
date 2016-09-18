#!/usr/bin/guile -s
!# ;; CONSpiracy v 0.1 by drcz, last touch 2016-09-18. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-modules (srfi srfi-1) (ice-9 nice-9) (ice-9 pretty-print))

;; Contents: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. "types"
;; 2. environments [bindings]
;; 3. evaluator
;; 4. REPL

;; 1. "types" ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;; 2. environments (bindings) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (lookup s env) (assoc-ref env s))
(define (insert s v env) `((,s . ,v) . ,env))
(define (update s v env) (insert s v (alist-delete s env)))

(define *initial-env*
  `([Y . (bind (f) ((bind (x) (x x)) (bind (g) (f (bind as ((g g) . as))))))]
    ;; primitive operations map to "real" procedures:
    [+ . ,+]
    [- . ,-]
    [* . ,*]
    [= . ,equal?]
    [< . ,<]
    [++ . ,string-append]
    [substring . ,substring] #;(substring s from to)
    [string-length . ,string-length]
    [atom? . ,(lambda (e) (not (pair? e)))]
    [numeral? . ,numeral?]
    [string? . ,string?]
    [truth-value? . ,truth-value?]))

;; 3. evaluator ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 3a. stripping syntactic sugar: ............................................
(define (and->ifs es) (fold-right (lambda (h t) (if t `(if ,h ,t #f) h)) #f es))
(define (or->ifs es)  (fold-right (lambda (h t) (if t `(if ,h #t ,t) h)) #f es))
(define (let->lambda bindings expr)
  (fold-right (lambda ((v e) t) `((bind (,v) ,t) ,e)) expr bindings))
#;(e.g (let->lambda '((x 2) (y 3) (z (+ x y))) '(* z z))
     ===> '((bind (x) ((bind (y) ((bind (z) (* z z)) (+ x y))) 3)) 2))

;;; 3b. the heart of it all: ..................................................
(define (Eval expr binding defs)
  (match expr    
    [(? constant? c) c]
    [(? variable? v) (match (lookup v binding)
		       [#f (Eval (lookup v defs) binding defs)]
		       [val val])]
    [('bind . cases) `(&bind ,cases ,binding)]
    [('let bindings e) (Eval (let->lambda bindings e) binding defs)]
    [('quote e) e]
    [('quasiquote e) (let qq-eval ((exp e))
		       (match exp
			 [('unquote e) (Eval e binding defs)]
			 [(h . t) `(,(qq-eval h) . ,(qq-eval t))]
			 [e e]))]
    [('if pre con alt) (if (Eval pre binding defs)
			   (Eval con binding defs)
			   (Eval alt binding defs))]
    [('and . es) (Eval (and->ifs es) binding defs)]
    [('or . es) (Eval (or->ifs es) binding defs)]
    [('not e) (Eval `(if ,e #f #t) binding defs)]
    [(rator . (? variable? rands)) (Apply (Eval rator binding defs)
				      (Eval rands binding defs)
				      defs expr)]
    [(rator . rands) (Apply (Eval rator binding defs)
			    (map (lambda (e) (Eval e binding defs)) rands)
			    defs expr)]
    [e (error `(error evaluating ,e) defs)]))

(define (Apply rator rands defs #;and-for-debug: expr)
  (match `(,rator . ,rands)
    [((? primitive? p) . rands) #;todo:typechecking-here? (apply p rands)]
    [(('&bind cases env) . vals)
     (let try-match ((cases cases))
       (match cases
	 [()
	  (error `(no match in ,expr) defs)]
	 [(pattern body . cases)
	  (match (bind pattern vals '() defs)
	    [#f (try-match cases)]
	    [binding (Eval body (append binding env) defs)])]))]
    [_ (error `(unknown application form ,expr) defs)]))

;;; 3c. the mystic patternmatching: ...........................................
(define (bind pattern form binding defs)
  (match pattern
    [(? constant? c) (and (equal? c form) binding)]
    [('quote e) (and (equal? e form) binding)]
    [('? pred v) (let ([val (lookup v binding)])
		   (if val
		       (and (Eval `(,pred (quote ,val)) binding defs) binding)
		       (and (Eval `(,pred (quote ,form)) binding defs)
			    (insert v form binding))))]
    [('? pred) (and (Eval `(,pred (quote ,form)) binding defs) binding)]
    ['_ binding]
    [(? variable? v) (let ([val (lookup v binding)])
		       (if val
			   (and (equal? val form) binding)
			   (insert v form binding)))]
    [(p . ps) (and-let* ([(f . fs) form]
			 [binding0 (bind p f binding defs)])
		(bind ps fs binding0 defs))]
    [e (error `(syntax error in pattern ,pattern -- ,e) defs)]))

;; 4. REPL ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (error msg topenv) (repl msg topenv)) ; :D

(define (repl out topenv)
  (write out) (newline) (display '>)
  (match (read)
    [('def s e) (repl `(new shorthand ,s memoized) (update s e topenv))]
    [('halt) (display "Auf Wiedersehen!") (newline) (exit)]
    [('show-topenv) (display-topenv topenv) (repl `(so now you know.) topenv)]
    [e (repl (Eval e '() topenv) topenv)]))

(define (display-topenv topenv)
  (match topenv
    [() 'akuku]
    [((s . e) . remaining)
     (display s) (display " <- ") (display e) (newline)
     (display-topenv remaining)]))

(begin ;; RUN
  (display "(-- ALGORITHMIC LANGUAGE CONSpiracy v0.1 --)") (newline)
  (display "  copyleft 2016/09/09-18 by Scislav Dercz   ") (newline)
  (display "type (halt) to quit") (newline)
  (newline)
  (repl 'READY. *initial-env*))

;; -- the end -- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
