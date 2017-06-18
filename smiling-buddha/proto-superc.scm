(use-modules (grand scheme) (ice-9 pretty-print))
(add-to-load-path (getcwd)) ;; make geiser happy...
(include-from-path "some-language-stuff.scm")

;;;; simplifier ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; take novum, cf meta-match...
(define (contains-jokers? expr)
  (match expr
    ['&JOKER #t]
    [(x . xs) (or (contains-jokers? x) (contains-jokers? xs))]
    [_ #f]))
(e.g. (contains-jokers? '(2 . &JOKER)))
(e.g. (not (contains-jokers? '(2 . 3))))

(define (simplified expr #;wrt metabinding)
  (let simp ((expr expr))
    (match expr
      [(? constant? c) c]
      [(? variable? v)
       (let ([val (lookedup v metabinding)])
	 (if (contains-jokers? val) v val))] ;; no need to simplify this further
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

(e.g. (simplified '(if (= x y) `(,x) `(x ,x y ,y)) '([x . (APPLY f x)] [y . 1]))
      ===> (if (= (APPLY f x) 1) `(,(APPLY f x)) `(x ,(APPLY f x) y 1)))
;;; no i nie wiem... to już???
(e.g. (simplified '(APPLY + 2 3) '()) ===> 5) ;; fajnie, nie?
(e.g. (simplified '(APPLY * 0 x) '([x . x])) ===> 0)
(e.g. (simplified '(APPLY * x x) '([x . x])) ===> (* x x))


;;;; applications-collector ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (all-applications #;in expr)
  (match expr
    [('APPLY . as) `(,expr . ,(append-map all-applications as))]
    [('quasiquote qq) (append-map-unquote all-applications qq)]
    [('if p c a) (append (all-applications p)
			 (all-applications c)
			 (all-applications a))]
    [((? primop-symbol?) . as) (append-map all-applications as)]
    [_ '()]))

#;(map pretty-print
     (all-applications '(APPLY (APPLY `(0) x y) 23 (+ x y) (APPLY `(1) x))))


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
      [(p . ps) (and-let* ([(e . es) mexpr]
			   [result0 (binding e p result)])
		  (binding es ps result0))]
      [otherwise `ERROR-SKURWESYN])))

(e.g. (matching '(2 3 4) '(x y z)) ===> ((z . 4) (y . 3) (x . 2)))
(e.g. (matching '(2 3 2) '(x y x)) ===> ((y . 3) (x . 2)))
(e.g. (matching '(2 3 3) '(x y x)) ===> #f)
(e.g. (matching '(2 &JOKER &JOKER) '(x y x)) ===> ((y . &JOKER) (x . 2)))
(e.g. (matching '(&JOKER &JOKER 2) '(x y x)) ===> ((x . 2) (y . &JOKER)))
(e.g. (matching '((2 . &JOKER)) '(a)) ===> ((a . (2 . &JOKER))))


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


;;; now something to compute proper "program-points"...
;;; ah shit, but we do have to check the innermost APPLY first,
;;; in case of desicion to inline some things change [especially
;;; the argument for outer APPLY will not have to be &JOKER].
;;; so we need to work in cycles -- check innermost APPLYies, compute their
;;; process branch, in case of non-recursice one inline the result (and
;;; remove the branch), then come back to the computed body, gather applications
;;; again, omitting the ones already computer but not inlined, and do so until
;;; all are "solved" [i.e. each is either inlined, or present in process tree].
;;; this is nb how previous DERC did operate.

;;; todo:
;;; -- computing [meta]arguments (with &JOKERs) for applications
;;; -- [meta]matching all applicable branches of APPLY with (matching ...),
;;;    simplilying with (simplified ...) and then processed,
;;; -- a whistle for applications [ignoring that first argument is numeral?]
;;; -- building and re-building the process tree using the above...
;;; (...)

