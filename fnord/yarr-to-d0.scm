(use-modules (ice-9 nice-9) (srfi srfi-1) (ice-9 pretty-print))
(define member? member) ; he_he

;;; note this one does not get rid of "duplications";
;;; it should be able to identify alpha-equivalent lambdas,
;;; so that the lambdas-explosion of d3-to-yarr.scm could be tamed a bit.
;;; and just think what will happen if we first cps-ize yarr code...

;;; -> this is a nice point to stop this nonsense.

(define (atom? x) (not (or (null? x) (pair? x)))) ;; ah! () should not be an atom?? -> at least for (f . a) etc.

(define *prim-env* ;; just copied y'know
  `((truth-value? . ,boolean?) (atom? . ,atom?) (numeral? . ,number?)
    (= . ,equal?) (cons . ,cons) (car . ,car) (cdr . ,cdr)
    (+ . ,+) (- . ,-) (* . ,*) (< . ,<)))
(define *primops* (map car *prim-env*)) ;; :D
(define (primop? p) (member? p *primops*)) ;; :]

(define (mk-list-constr xs) (fold-right (lambda (h t) `(cons ,h ,t)) '() xs))

(define (gather-lambdas expr)
  (match expr
    [(or (? number?) (? boolean?) (? null?)) '()]    
    [(? symbol?) '()] ; includes primops!
    [('quote _) '()]
    [('if p c a) (lset-union equal?
			     (gather-lambdas p)
			     (gather-lambdas c)
			     (gather-lambdas a))]
    [('lambda as b) (lset-union equal?
			   `(,expr)
			   (gather-lambdas b))]
    [(f . (? atom?)) (gather-lambdas f)]
    [(f . args) (apply lset-union equal? (map gather-lambdas expr))]))


(define (free-vars-of expr)
  (match expr
    [(or (? number?) (? boolean?) (? null?)) '()]
    [(? primop?) '()] ;; WATCH OUT, it's NOT safe, var can have primop's name...
    [(? symbol? s) `(,s)]
    [('quote _) '()]
    [('if p c a) (lset-union equal?
			     (free-vars-of p)
			     (free-vars-of c)
			     (free-vars-of a))]
    [('lambda as b) (lset-difference equal?
				(free-vars-of b)
				(if (atom? as) `(,as) as))]
    [(f . (? atom? a)) (lset-union equal? (free-vars-of f) (free-vars-of a))]
    [(f . args) (apply lset-union equal? (map free-vars-of expr))]))

;(free-vars-of '((lambda (x) (f x y)) (+ a b)))

;;; (<l> . (<n> <args> <fvs>)) ? -> chyba ta.

(define (mk-vars-to-positions-mapping varlist source)
  (if (atom? varlist)
      `[(,varlist . ,source)]
      (let loop ((varlist varlist)
		 (deepest source))
	(if (null? varlist)
	    '()
	    `((,(car varlist) . (car ,deepest))
	      . ,(loop (cdr varlist) `(cdr ,deepest)))))))
;(mk-vars-to-positions-mapping '(a b c) 'args)

(define (generate-code-for body argnames freevars)
  (let* ((args-remap (mk-vars-to-positions-mapping argnames 'args))
	 (freevars-remap (mk-vars-to-positions-mapping freevars '(cdr label)))
	 (remapping (append args-remap freevars-remap)))
    `[(lambda ,(map car remapping) ,body) . ,(map cdr remapping)]))

(define (compile yarr-prog)
  (let* ([lambdas (gather-lambdas yarr-prog)]
	 [labels (map (lambda (nr lmbd) `(,lmbd . (,(1+ nr) . ,(free-vars-of lmbd))))
		      (iota (length lambdas)) lambdas)]
	;[build-label (lambda (lmbd) `(MK-LABEL . ,(assoc-ref labels lmbd)))]
	 [build-label (lambda (lmbd) (mk-list-constr (assoc-ref labels lmbd)))]
	 [defunctionalize
	   (lambda (expr)
	     (let d17n ((expr expr))
	       (match expr
		 [(or (? number?) (? boolean?) (? null?)) expr]
		 [(? symbol?) expr]
		 [('quote _) expr]
		 [('if p c a) `(if ,(d17n p) ,(d17n c) ,(d17n a))]
		 [('lambda a b) (build-label expr)]
		 ;;; actually it should be:
		 ;;; -- for unary primop (eg car) `(,f (car ,(d17n a)))
		 ;;; -- for binary primop (eg +) (let ((a0 (d17n a)))
		 ;;;                               `(,f (car ,a0) (car (cdr ,a0))))
		 [((? primop? f) . (? atom? a)) `(,f . ,(d17n a))] ; !!!!
		 ;;; \actually
		 [(f . (? atom? a)) `(APPLY ,(d17n f) ,(d17n a))]
		 [((? primop? f) . args) `(,f . ,(map d17n args))]
		 [(f . args) `(APPLY ,(d17n f)
				     ,(mk-list-constr (map d17n args)))])))]
	 [bodies (map (lambda (lmbd) ;; <lbl, args, body> ??
			(let ((label (assoc-ref labels lmbd))
			      (args (cadr lmbd))
			      (body (defunctionalize (caddr lmbd))))
			  `(,label ,args ,body)))
		      lambdas)]
	 [main `((0) ,(free-vars-of yarr-prog) ,(defunctionalize yarr-prog))]
	 [branches `(,main . ,bodies)]
	 [body-of-apply
	  (fold-right (lambda (((id . fvs) argnames body) rest)
			`(if (= (car label) ,id)
			     ,(generate-code-for body argnames fvs)
			     ,rest))
		      '(ERROR) ;; ...or "halt"?
		      branches)])
    ;; now just generate the output d0/kln program...
    `[(APPLY '(0) ())
      (APPLY . (lambda (label args) ,body-of-apply))]))

(pretty-print
 (compile (read)))
(exit)

;;; but this naive implementation, even if it works, makes no sense,
;;; as DERC does not know partially-static data...
;;; so now we should implement them in DERC, or revert to lambda-lifting
;;; whenever the called function is known.


;;;;;;;;;; tests etc... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(pretty-print
 (compile '((lambda (x y) (lambda (z) (+ x (* z y)))) 2 (* 7 8))))

(newline)
(pretty-print
 (compile '(lambda (z) (+ x (* z y)))))

(newline)
(pretty-print
 (compile '(lambda (x y z) (+ x ((lambda (x) (* x x)) (+ y z))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define t1
  '[
(((lambda (f)
    ((lambda (x) (x x))
     (lambda (g) (f (lambda args ((g g) . args))))))
  (lambda (map)
    (lambda (f xs)
      (((lambda (f)
          ((lambda (x) (x x))
           (lambda (g) (f (lambda args ((g g) . args))))))
        (lambda (fold-r)
          (lambda (xs e op)
            (if (= xs ())
              e
              (op (car xs) (fold-r (cdr xs) e op))))))
       xs
       ()
       (lambda (h t) (cons (f h) t))))))
 ((lambda (f)
    ((lambda (x) (x x))
     (lambda (g) (f (lambda args ((g g) . args))))))
  (lambda (f)
    (lambda (n) (if (= n 0) 1 (* n (f (- n 1)))))))
 (((lambda (f)
     ((lambda (x) (x x))
      (lambda (g) (f (lambda args ((g g) . args))))))
   (lambda (map)
     (lambda (f xs)
       (((lambda (f)
           ((lambda (x) (x x))
            (lambda (g) (f (lambda args ((g g) . args))))))
         (lambda (fold-r)
           (lambda (xs e op)
             (if (= xs ())
               e
               (op (car xs) (fold-r (cdr xs) e op))))))
        xs
        ()
        (lambda (h t) (cons (f h) t))))))
  (((lambda (f)
      ((lambda (x) (x x))
       (lambda (g) (f (lambda args ((g g) . args))))))
    (lambda (mk-adder)
      (lambda (x) (lambda (y) (+ x y)))))
   3)
  '(1 2 3 4 5)))
])

#;(map (lambda (l)
       (pretty-print l)
       (pretty-print `(FV = ,(free-vars-of l)))
       (newline) (newline))
     (gather-lambdas t1))

(write `(now the controversial compilation will take place... or not!)) (newline)
(pretty-print (compile t1))
