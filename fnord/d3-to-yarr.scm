(use-modules (ice-9 pretty-print) (ice-9 nice-9))
(define member? member)
(define (atom? x) (not (pair? x)))

(define (lookup s env)
  (match env
    [() '&UNBOUND]
    [((s0 . v0) . env) (if (eq? s s0) v0 (lookup s env))]))

(define *prim-env* ;; just copied y'know
  `((truth-value? . ,boolean?) (atom? . ,atom?) (numeral? . ,number?)
    (= . ,equal?) (cons . ,cons) (car . ,car) (cdr . ,cdr)
    (+ . ,+) (- . ,-) (* . ,*) (< . ,<)))
(define *primops* (map car *prim-env*)) ;; :D
(define *Y* '(lambda (f) ((lambda (x) (x x)) (lambda (g) (f (lambda args ((g g) . args)))))))

(define (inline expression definitions)
  (let process ([expression expression]
		[bound-vars *primops*]
		[inlined '()])
    (match expression
      [(or (? number?) (? boolean?) (? null?) ('quote _)) expression]
      [(? symbol? s) (if (member? s (append inlined bound-vars))
			 s
			 `(,*Y* (lambda (,s) ,(process (lookup s definitions)
						  *primops*
						  `(,s . ,inlined)))))]
      [('lambda (? atom? a) b) `(lambda ,a ,(process b
					   (cons a bound-vars)
					   inlined))]
      [('lambda as b) `(lambda ,as ,(process b
				   (append as bound-vars)
				   inlined))]
      [('if p c a) `(if ,(process p bound-vars inlined)
			,(process c bound-vars inlined)
			,(process a bound-vars inlined))]
      [(f . (? atom? a)) `(,(process f bound-vars inlined)
			   . ,(process a bound-vars inlined))]
      [(f . as) (map (lambda (e) (process e bound-vars inlined)) `(,f . ,as))])))

(define (d3->yarr program)
  (let ([(expression . definitions) program])
    (inline expression definitions)))

(pretty-print (d3->yarr (read)))
(exit)


;;;;;;;;;;;;;;;;;;;;
(define p1 '[(map f (map (mk-adder 3) '(1 2 3 4 5)))
 (mk-adder . (lambda (x) (lambda (y) (+ x y))))
 (f . (lambda (n) (if (= n 0) 1 (* n (f (- n 1))))))
 (fold-r . (lambda (xs e op) (if (= xs ()) e (op (car xs) (fold-r (cdr xs) e op)))))
 (map . (lambda (f xs) (fold-r xs () (lambda (h t) (cons (f h) t)))))
 #;(map . (lambda (f xs) (if (= xs ()) () (cons (f (car xs)) (map f (cdr xs))))))])

(inline (car p1) (cdr p1))
