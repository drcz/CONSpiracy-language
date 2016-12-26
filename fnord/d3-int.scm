(use-modules (ice-9 match))

(define (atom? x) (not (pair? x)))

(define (lookup s env)
  (match env
    [() '&UNBOUND]
    [((s0 . v0) . env) (if (eq? s s0) v0 (lookup s env))]))
    
;;; language implementation:
(define (Eval expr env topenv)
  (let E ((expr expr))
    (match expr
      [(or (? number?) (? boolean?) (? null?) ('&proc _ _ _)) expr]
      [(? symbol? v) (match (lookup v env)
		       ['&UNBOUND (Eval (lookup v topenv) prim-env topenv)] 
		       [e e])]
      [('quote e) e]
      [('if p c a) (if (E p) (E c) (E a))]
      [('lambda as b) `(&proc ,as ,b ,env)]
      [(f . vs)
       (match `(,(E f) . ,(if (atom? vs) (E vs) (map E vs)))
	 [(('&proc (? atom? a) b env) . vs)
	  (Eval b `((,a . ,vs) . ,env) topenv)]
	 [(('&proc as b env) . vs)
	  (Eval b (append (map cons as vs) env) topenv)]
	 [((? procedure? p) . vs)
	  (apply p vs)])])))

;;; now just define some primitives:
(define prim-env
  `((truth-value? . ,boolean?) (atom? . ,atom?) (numeral? . ,number?)
    (= . ,equal?) (cons . ,cons) (car . ,car) (cdr . ,cdr)
    (+ . ,+) (- . ,-) (* . ,*) (< . ,<)))

;;; + the i/o shit:
(let* ((program (read))
       (expr (car program))
       (defs (cdr program)))
;  (display topenv) (newline)
  (display (Eval expr prim-env defs))
  (newline))
(exit)
