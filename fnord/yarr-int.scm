(use-modules (ice-9 match))
(define (atom? x) (not (or (null? x) (pair? x))));(define (atom? x) (not (pair? x)))
;;; language implementation:
(define (Eval expr env)
  (let E ((expr expr))
    (match expr
      [(or (? number?) (? boolean?) (? null?) ('&proc _ _ _)) expr]
      [(? symbol? v) (assoc-ref env v)]
      [('quote e) e]
      [('if p c a) (if (E p) (E c) (E a))]
      [('lambda as b) `(&proc ,as ,b ,env)]
      [(f . vs)
       (match `(,(E f) . ,(if (atom? vs) (E vs) (map E vs)))
	 [(('&proc (? atom? a) b env) . vs) (Eval b `((,a . ,vs) . ,env))]
	 [(('&proc as b env) . vs) (Eval b (append (map cons as vs) env))]
	 [((? procedure? p) . vs) (apply p vs)])])))
;;; now just define some primitives:
(define prim-env
  `((truth-value? . ,boolean?) (atom? . ,atom?) (numeral? . ,number?)
    (= . ,equal?) (cons . ,cons) (car . ,car) (cdr . ,cdr)
    (+ . ,+) (- . ,-) (* . ,*) (< . ,<)))
;;; + the i/o shit:
(display (Eval (read) prim-env)) (newline)
(exit) ;;; boom.

;;; test suite: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-modules (ice-9 pretty-print))
(map pretty-print
     `[,(Eval '23 prim-env)
       ,(Eval '(+ 2 3) prim-env)
       ,(Eval '((lambda (x) (* x x)) (+ 2 3)) prim-env)
       ;; factorial classic:
       ,(Eval '[((lambda (f) ((lambda (x) (x x)) (lambda (g) (f (lambda args ((g g) . args))))))
		 (lambda (fac)
		   (lambda (n)
		     (if (= n 0) 1 (* n (fac (- n 1))))))) 5] prim-env)
       ;; concatenate 2 lists classic:
       ,(Eval '[((lambda (f) ((lambda (x) (x x)) (lambda (g) (f (lambda args ((g g) . args))))))
		 (lambda (apd)
		   (lambda (xs ys)
		     (if (= xs ()) ys (cons (car xs) (apd (cdr xs) ys))))))
		'(f u c k) '(- y o u)] prim-env)])
;;; ...clearly it works.
