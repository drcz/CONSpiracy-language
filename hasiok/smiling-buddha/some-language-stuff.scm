;; i don't always program, but when i do, i prefer (grand scheme).
(use-modules (grand scheme))
(define ((is? x) y) (equal? x y)) ;; lulz.

;;; some "language stuff"... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (constant? x) (or (null? x)
			  (numeral? x)
			  (truth-value? x)
			  (primop-symbol? x)))
(define numeral? number?)
(define truth-value? boolean?)
(define (primop-symbol? x)
  (and (symbol? x)
       (member? x '(= + - * truth-value? atom? numeral? bind-form?))))
(define (variable? x) (and (symbol? x) (not (constant? x))))

(define (append-map-unquote f qq) ;; WAT?? ;)
  (match qq
    [('unquote x) (f x)]
    [(h . t) (append (append-map-unquote f h) (append-map-unquote f t))]
    [something '()]))


(define (map-unquote f qq)
  (match qq
    [('unquote x) `(,'unquote ,(f x))]
    [(h . t) `(,(map-unquote f h) . ,(map-unquote f t))]
    [something something]))

;;;;; this part is stinky but it will become beautiful some day.
;;;;; [not that the rest is much better, but...]
(define (cons<-qqexpr qqexpr)
  (match qqexpr
    [() '(quote ())]
    [(? symbol? s) `(quote ,s)]
    [('unquote e) (let dry-run ((expr e))
		    (match expr
		      [('quasiquote qqe) (cons<-qqexpr qqe)]
		      [('quote e) expr]
		      [(f . (? pair? args)) `(,f . ,(map dry-run args))] ;;?!
		      [_ expr]))]
    [(hd . tl) `(cons ,(cons<-qqexpr hd) ,(cons<-qqexpr tl))]))

(define (qqexpr<-cons expr)
  (match expr
    [(? constant? c) c]
    [(? variable? v) `(,'unquote ,v)]
    [('quote e) e]
    [('cons hd tl) `(,(qqexpr<-cons hd) . ,(qqexpr<-cons tl))]
    [e `(,'unquote ,e)]))
;;;; end of stinky part.

(define (simplest-qq qq) (qqexpr<-cons (cons<-qqexpr qq)))

(e.g. (simplest-qq '(,`qwe a (b . c) (,'d . ,`(e f)) . ,'(hi there!)))
      ===> (qwe a (b . c) (d e f) hi there!))


;;;; environments... ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; some better names would be great. also, this "lookedup" should return
;;; #f on fail and pair (k . v) otherwise...
(define (lookedup sym alist) #;(or (assoc-ref alist sym) '&UNBOUND)
  (match alist
    [() '&UNBOUND]
    [([(? (is? sym)) . val] . _) val]
    [(_ . alist) (lookedup sym alist)]))
  
(define (updated env #;on var #;binding expr)
  `((,var . ,expr) . ,(removed var env)))

(define (removed var #;from env)
  (match env
    [() '()]
    [([(? (is? var)) . val] . env*) env*]
    [(vv . env*) `(,vv . ,(removed var env*))]))


;; (...)
