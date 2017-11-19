;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The syntax of CONSpiracy compedia.
;;; / this is mostly for your information -- the implementation repeats some
;;;   of this information. /

(use-modules (grand scheme))
(define ((list-of p?) xs) (and (list? xs) (every p? xs)))


(define numeral? number?) ;; disgusting lies anyway TODO: maybe integers only?
(define truth-value? boolean?) ;;; TODO sure?

(define (expression? e)
  (or (null? e)
      (numeral? e)
      (symbol? e)
      (truth-value? e)
      (string? e)
      (and (pair? e)
           (expression? (car e))
           (expression? (cdr e)))))

[e.g. (not (expression? (lambda (x) x)))]
[e.g. (not (expression? #(1 2 3)))]

(define (primop? x) (member? x '(&atom? &str? &num? &tv? &closure?
                                 &eq? 
                                 &lt? &add &mul &sub &div &mod
                                 &strcat &substr &strlen)))


(define (constant? x)
  (or (null? x)
      (numeral? x)
      (truth-value? x)
      (primop? x)
      (string? x)))

(define (identifier? x)
  (and (symbol? x) (not (eq? (first (string->list (symbol->string x))) '#\&))))

[e.g. (identifier? 'identifier)]
[e.g. (not (identifier? '&closure))]


(define (pattern? x)
  (match x
    ['_ #t]
    [() #t]
    [(? identifier?) #t]
    [('? (? form?)) #t]
    [('? (? form?) (? identifier?)) #t]
    [('quote (? expression?)) #t]
    [(h . t) (and (pattern? h) (pattern? t))]
    [_ #f]))

[e.g. (pattern? '('concat (x . xs) ys))]


(define (form? x)
  (or (constant? x)
      (identifier? x)
      (phi-form? x)
      (let-form? x)
      (quote-form? x)
      (quasiquote-form? x)
      (if-form? x)
      (and-form? x) (or-form? x) (not-form? x)
      (application? x)))


(define (phi-form? x)
  (or #;(and-let* ([('bind (? pattern?) (? form?)) x])) ;; ...
      (and-let* ([('phi [(? pattern?) (? form?)] ...) x]))))

(define (let-form? x)
  (and-let* ([('let [(? pattern?) (? form?)] ... (? form?)) x])))


(define (quote-form? x) (and-let* ([('quote (? expression?)) x])))


(define (quasiquote-form? x)
  (and-let* ([('quasiquote qqe) x])
    (let proper-qqe? ([expr qqe])
      (match expr
        [('unquote e) (form? e)]
        [(h . t) (and (proper-qqe? h) (proper-qqe? t))]
        [(? expression?) #t]
        [_ #f]))))


(define (if-form? x) (and-let* ([('if (? form?) (? form?) (? form?)) x])))

(define (and-form? x) (and-let* ([('and (? form?) ...) x])))
(define (or-form? x) (and-let* ([('or (? form?) ...) x])))
(define (not-form? x) (and-let* ([('not (? form?)) x])))


(define (application? x)
  (and (pair? x)
       (not (constant? (first x)))
       (or (form? (cdr x))
           ((list-of form?) x))))

[e.g. (application? '(f))]
[e.g. (application? '(f . x))]
[e.g. (application? '(f x))]
[e.g. (application? '(f x y z))]


;[e.g. (phi-form? '(phi (x) (* x x)))]

[e.g. (phi-form? '(phi [(()       ys) ys]
                       [((x . xs) ys) `(,x . ,(cat xs ys))]))]

[e.g. (phi-form? '(phi [x x]))]

[e.g. (let-form? '(let ([x (f a b c)]
                        [(current . rest) remaining])
                    (g current x)))]

[e.g. (quasiquote-form? '`(3 + 5 = ,(+ 3 5)))]



(define (definition? x) (and-let* ([('def (? identifier?) (? form?)) x])))
[e.g. (definition? '(def square (phi [(x) (* x x)])))]

(define (theorem? x) (and-let* ([('thm. (? form?)) x])))
[e.g. (theorem? '(thm. (= (concat (concat xs ys) zs) (concat xs (concat ys zs)))))]

(define (example? x) (and-let* ([('e.g. (? form?) '===> (? expression?)) x])))
[e.g. (example? '(e.g. (concat '(q w e) '(a s d)) ===> (q w e a s d)))]


(define (entry? x)
  (or (definition? x)
      (theorem? x)
      (example? x)))


(define compendium? (list-of entry?))

[e.g. (compendium?
       '[ (def magickal-constant (+ 90 3))

          (def foldr (phi [(_ e ()) e]
                          [(op e (x . xs)) (op x (foldr op e xs))]))

          (def map (phi [(f xs) (foldr (phi (h t) `(,(f h) . ,t)) () xs)]))
          (def square (phi [(x) (* x x)]))

          (e.g. (map square '(1 2 3)) ===> (1 4 9))
          
          (def sum (phi [(xs) (foldr + 0 xs)]))
          
          (def sum-of-squares (phi [(xs) (sum (map square xs))]))

          (thm. (< (sum xs) (sum-of-squares xs))) ])]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the interpreter will work on simplified forms...

(define (desugared form)
  (match form

    ;;; this one is fucked up as it's ambiguous
    #;[('phi (? pattern? p) (? form? f*))
     `(phi [,p ,(desugared f*)])]

    ;;; and/or/not are just sugar for ifs (TODO: for now?)
    [('and . fs*)
     (fold-right (lambda (f* fs) (let ([f (desugared f*)])
                              (if fs `(if ,f ,fs #f) f)))
                 #f
                 fs*)]
    [('or . fs*)
     (fold-right (lambda (f* fs) (let ([f (desugared f*)])
                              (if fs `(if ,f #t ,fs) f)))
                 #f
                 fs*)]
    [('not f*)
     `(if ,(desugared f*) #t #f)]

    ;;; let's are just sugar for nested phi-forms (TODO: for now?)
    [('let bnds* f*)
     (fold-right (lambda ((pat frm*) bs) `((phi [(,pat) ,bs]) ,(desugared frm*)))
                 (desugared f*)
                 bnds*)]
    
    ;;; propagate desugaring into subforms...
    [('phi . cases)
     `(phi . ,(map (lambda ((p f*)) `(,p ,(desugared f*))) cases))]

    [('if p* c* a*)
     `(if ,(desugared p*) ,(desugared c*) ,(desugared a*))]

    [('quasiquote qqe*)
     `(,'quasiquote ,(let desugared-qq ([expr qqe*])
                       (match expr
                         [('unquote e) `(,'unquote ,(desugared e))]
                         [(h . t) `(,(desugared-qq h) . ,(desugared-qq t))]
                         [_ expr])))]

    [(f* . as*)
     `(,(desugared f*) . ,(if (list? as*) (map desugared as*) (desugared as*)))]

    ;;; gucci.
    [_ form]))


;[e.g. (desugared '(bind (x) (* x x))) ===> (bind [(x) (* x x)])]
[e.g. (desugared '(phi [(x) (* x x)])) ===> (phi [(x) (* x x)])]

[e.g. (desugared '(phi [(x) (* x x)]
                       [(x y) (+ x y)]))
      ===> (phi [(x) (* x x)]
                [(x y) (+ x y)])]

[e.g. (desugared '`(q w e (not important) ,(let ([(y . ys) x]
                                                 [x (f x)])
                                             (and a b c))))
      ===> `(q w e (not important)
               ,[(phi [((y . ys)) [(phi [(x) (if a (if b c #f) #f)]) (f x)]]) x])]

;;; TODO unit tests for desugared...
