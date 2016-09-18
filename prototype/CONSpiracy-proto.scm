#!/usr/bin/guile -s
!# ;; CONSpiracy v 0.1 by drcz, last touch 2016-09-18, Eindhoven ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; the author is extremely grateful to Panicz Godek for nice-9 module,
;; and to euro-garden coffeeshop, for serving excelent coffee :)
(use-modules (srfi srfi-1) (ice-9 nice-9) (ice-9 pretty-print))

;; currently todo: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; -- a simplest compiler (...)
;; -- interactive systems as first class citizens (...)
;; -- editor/"ide" (...)

;; Contents: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0. The Algorithmic Language CONSpiracy.
;; 1. "Types".
;; 2. Environments [bindings].
;; 3. Evaluator.
;; 4. REPL.
;; appendix. Examples.

;; 0. The Algorithmic Language CONSpiracy. ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The Algorithmic Language CONSpiracy is an applicative, functional program-
;; ming language with dynamic typing and lexical scoping. An expression can be
;; AN ATOM, e.g.:
;;;;; 23 ;; numeral
;;;;; "hi!" ;; string
;;;;; #t ;; truth-value
;;;;; (&bind ...) ;; bind-form ("a procedure")
;;;;; x ;; symbol ("a variable")
;; or A FORM, e.g.:
;;;;; (+ 2 3) ;; primitive op. application
;;;;; (+ 2 (* 7 8)) ;; nested pr.op.app.
;;;;; (if (= x y) x y) ;; conditional expression
;;;;; `(2 + 3 = ,(+ 2 3)) ;; quasiquote
;;;;; (bind (0) 1 (n) (* n (f (- n 1)))) ;; bind-form ("a lambda")
;;;;; etc...

;; Each expression e given a context (i.e. environment) has its value, which
;; depends on: (a) e alone, if it's a constant, (b) environment and e if it's
;; a symbol, or (c) type of "operatior" (i.e. first element of list representing
;; the form) and values of following subexpressions ("operands").

;; Constants, e.g.:
;;;;; > 23
;;;;; 23
;;;;; > "a string"
;;;;; "a string"

;; Variables, e.g.:
;;;;; > x
;;;;; (unbound symbol x)
;;;;; > (let ((x 2) (y 3)) (+ x y)) ;; two forms here actually!
;;;;; 5

;; ...and now all the forms:
;; (1) A QUOTE FORM is (quote <e>) or shorter '<e> for any expression <e>,
;; and it evaluates to <e>, e.g.:
;;;;; > 'hi!
;;;;; hi!
;;;;; > '(+ 2 3)
;;;;; (+ 2 3)

;; (2) a QUASIQUOTE FORM is (quasiquote <qe>) for expression possibly containing
;; unquote forms; it's value is expression <qe> with any (unquote <e>) (or ,<e> in
;; short) replaced with the value of <e>, e.g.
;;;;;; > `(hey! 2 + 3 = ,(+ 2 3))
;;;;;; (hey! 2 + 3 = 5)

;; (3) AN IF FORM is (if <pred> <concl> <alt>) and it's value depends on the value
;; of <pred> as follows: if it's #f, then if-form's value is the value of <alt>,
;; otherwise it's the value of <concl>. E.g.:
;;;;; > (if (= 2 2) 'nice 'boo)
;;;;; nice
;;;;; > (if (= 2 3) 'nice 'boo)
;;;;; boo

;; (4) AND-, OR- and NOT-FORMS are syntactic sugar for IF FORMS, e.g.
;; (and a b c) <=> (if a (if b c))

;; (5) BIND FORM is (bind p1 e1 ... pn en), it's value is a &bind object,
;; "a procedure", such that when applied to args finds the first pattern
;; pi that args matches, and evaluates to the value of ei (for i=1,...,n). E.g.:
;;;;; > (bind (x) (* x x))
;;;;; (&bind ((x) (* x x)) ())
;;;;; >((bind (x) (* x x)) 2)
;;;;; 4
;;;;; >((bind (x) (* x x)) (+ 2 3))
;;;;; ((bind (x) (* x x)) (+ 2 3))
;;;;; 25
;;;;; > ((bind (0) 1 _ 23) 0)
;;;;; 1
;;;;; > ((bind (0) 1 _ 23) 1)
;;;;; 23

;; [[todo: describe patterns -- for now cf def. of bind in (3c).]]

;; (6) LET FORM is (let ((v1 e1) ... (vn en)) e) and is syntactic sugar for
;; embedded BIND FORMS ((bind (vn) ... ((bind (v1) e) e1) ... ) en), e.g.
;;;;; > (let ((a 2) (b 3) (c (+ a b))) (* c c))
;;;;; 25

;; (*7*) MAGICKAL DEF FORM is (def <definiens> <definiendum>) for any symbol
;; <definiens> and any expression <definiendum>. It makes the interpreter
;; substitute the former for the latter in any evaluated expression. Therefore
;;;;;; > (def square (bind (x) (* x x)))
;;;;;;(new shorthand square memoized)
;;;;;; (+ (square 3) (square 4))
;;;;;; 25
;; Since it's binding is dynamic, it allows recursive definitions, such as:
;;;;;; > (def map (bind (_ ()) ()
;;;;;;                  (f (x . xs)) `(,(f x) . ,(map f xs))))
;;;;;; (new shorthand map memoized)
;;;;;; > (map square '(1 2 3 4 5))
;;;;;; (1 4 9 16 25)
;; -- this means actually that map stands for infinite expression of the form
;; (bind (_ ()) ()
;;       (f (x . xs)) `(,(f x) . ,((bind (_ ()) ()
;;                                       (f (x. xs)) `(,(f x) . ...
;;                                                              f
;;                                                              xs))) f xs)
;; (...?)

;; (8) Any other form is an application:
;; (8a) of primitive operator, e.g.
;;;;; > (+ 2 3)
;;;;; 5
;;;;; > (++ "hi " "there!")
;;;;; "hi there!"
;; (8b) of bind object -- cf (5).
;; ...

;; (...TODO)


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
    [+ . ,+] [- . ,-] [* . ,*] [= . ,equal?] [< . ,<] [++ . ,string-append]
    [substring . ,substring] [string-length . ,string-length]
    [atom? . ,(lambda (e) (not (pair? e)))] [numeral? . ,numeral?]
    [string? . ,string?] [truth-value? . ,truth-value?]))

;; 3. evaluator ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 3a. stripping syntactic sugar: ............................................
(define (and->ifs es) (fold-right (lambda (h t) (if t `(if ,h ,t #f) h)) #f es))
#;(e.g (and->ifs '(a b c)) ===> '(if a (if b c #f) #f))
(define (or->ifs es)  (fold-right (lambda (h t) (if t `(if ,h #t ,t) h)) #f es))
#;(e.g (or->ifs '(a b c)) ===> '(if a #t (if b #t c)))
(define (let->lambda bindings expr)
  (fold-right (lambda ((v e) t) `((bind (,v) ,t) ,e)) expr bindings))
#;(e.g (let->lambda '((x 2) (y 3) (z (+ x y))) '(* z z))
     ===> '((bind (x) ((bind (y) ((bind (z) (* z z)) (+ x y))) 3)) 2))

;;; 3b. the heart of it all: ..................................................
(define (Eval expr binding defs)
  (match expr    
    [(? constant? c) c]
    [(? variable? v) (match (lookup v binding)
		       [#f (Eval (match (lookup v defs)
				   [#f (error `(unbound symbol ,v))]
				   [expr expr])
				 binding
				 defs)]
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
  (display "   (-- ALGORITHMIC LANGUAGE CONSpiracy v0.1 --)") (newline)
  (display "copyleft by Scislav Dercz 2016/09/09-18, Eindhoven") (newline)
  (display "type (halt) to quit") (newline)
  (newline)
  (repl 'READY. *initial-env*))

;; appendix: for now cf conspiracy.cpr...
;; -- the end -- ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
