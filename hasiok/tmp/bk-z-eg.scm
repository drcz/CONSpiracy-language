;;; I don't always scheme, but when I do, I prefer (grand scheme).
(use-modules (grand scheme) (ice-9 pretty-print))

;;; some examples to work with:
(define apnd
  '[((('apd) ()       ys) #;=> ys)
    ((('apd) (x . xs) ys) #;=> `(,x . ,(APPLY '(apd) xs ys)))])

(define test
  '( [(('foldr) _  e ()      ) #;=> e]
     [(('foldr) op e (x . xs)) #;=> (APPLY op x (APPLY '(foldr) op e xs))]
     [(('map) f xs)            #;=> (APPLY '(foldr) `(LAM1 ,f) () xs)]
     [(('LAM1 f) h t)          #;=> `(,(APPLY f h) . ,t)]
     [(('LAM2) x)              #;=> `(,x ,x)]      
     [(('test) xs)             #;=> (APPLY '(map) '(LAM2) xs)]))


;;; let's go.

(define (alist-delete key alist) ;;; pfff...
  (match alist
    [() '()]
    [((k . v) . alist) (if (eq? k key) alist
			#;else `((,k . ,v) . ,(alist-delete key alist)))]))

(define (meta-binding pattern form bnd)
  (match pattern
    ['_ bnd]
    [() (and (or (null? form) (eq? form '?)) bnd)]
    [(? symbol? s) (match (assoc-ref bnd s)
		     [#f `((,s . ,form) . ,bnd)]
		     ['? `((,s . ,form) . ,(alist-delete s bnd))]
		     [trm (and (or (eq? form '?) (equal? trm form)) bnd)])]
    [('quote e) (and (or (eq? form '?) (equal? e form)) bnd)]
    [(p . ps) (and-let* ([(f . fs) (if (eq? form '?) '(? . ?) form)]
			 [bnd* (meta-binding p f bnd)])
		(meta-binding ps fs bnd*))]
    [else #f]))

[e.g. (meta-binding '(x . y) '(qwe ?) '()) ===> ((y . (?)) (x . qwe))]
[e.g. (meta-binding '(x x) '(qwe ?) '()) ===> ((x . qwe))]
[e.g. (meta-binding '(x (y z) x) '(? ? qwe) '()) ===> ((x . qwe) (z . ?) (y . ?))]

;;; but beware!
[e.g. (meta-binding '(x y) '(? (? ?)) '()) ===> ((y . (? ?)) (x . ?))]
;;; ...for now.
;;; the next, bolder version will make sure we have "enough variables to bind
;;; each joker separately" if you know what i mean (do i?).

(define (with-jokers? val)
  (match val
    ['? #t]
    [(v . vs) (or (with-jokers? v) (with-jokers? vs))]
    [_ #f]))

(define (pattern-instance #;for pattern #;wrt metabinding)
  (match pattern
    ['_ '_]
    [() '()]
    [(? symbol? s) (match (assoc-ref metabinding s)
		     [#f s]
		     [(? with-jokers?) s]
		     [val `(quote ,val)])]
    [('quote e) pattern]
    [(p . ps) `(,(pattern-instance p metabinding)
		. ,(pattern-instance ps metabinding))]))

[e.g. (pattern-instance '(x y x)
			(meta-binding '(x y x)
				      '(? dupa qwe)
				      '())) ===> ('qwe 'dupa 'qwe)]

[e.g. (pattern-instance '(x y) (meta-binding '(x y) '(+ (? ?)) '()))  ===> ('+ y)]


;;;; the following 2 are fucked up and only work in some cases
;;;; but there's no point in fixing this as we switch to working
;;;; with CONS representation only because it is unique
;;;; (e.g. (CONS 'x ()) vs `(x), `(,'x), `(x . ()), `(,'x . ,'()) etc.

(define (cons<-qqexpr qqe)
  (match qqe
    [() '() #;''()]
    [(? symbol? s) `(quote ,s)]
    [('unquote e) (let skipped ([e e])
		    (match e
		      [('quasiquote qqe) (cons<-qqexpr qqe)]
		      [('quote _) e]
		      [('APPLY . as) `(APPLY . ,(map skipped as))]
		      [_ e]))]
    [(h . t) `(CONS ,(cons<-qqexpr h) ,(cons<-qqexpr t))]))

(define (qqexpr<-cons ce)
  (match ce
    [() '()]
    [('quote e) e]
    [('CONS h t) `(,(qqexpr<-cons h) . ,(qqexpr<-cons t))]
    [e `(,'unquote ,e)]))

[e.g. (cons<-qqexpr '(hey ,x ,(APPLY f x)))
      ===> (CONS 'hey (CONS x (CONS (APPLY f x) ())))]
[e.g. (qqexpr<-cons '(CONS 'hey (CONS x (CONS (APPLY f x) ()))))
      ===> (hey ,x ,(APPLY f x))]
;;; and, more interestingly:
[e.g. (qqexpr<-cons (cons<-qqexpr '(a b ,`(c d . ,'(e f)) ,x)))
      ===> (a b (c d e f) ,x)]
[e.g. (qqexpr<-cons (cons<-qqexpr '(a b . ,`(c ,x . ,'(d e f)))))
      ===> (a b c ,x d e f)]

;;; ...and the proof of fucked-upness:
[e.g. (qqexpr<-cons (cons<-qqexpr '`(,x . ,(APPLY `(L ,f) x x))))
      ===> `(,x unquote (APPLY (CONS 'L (CONS f ())) x x)) #;CO-ZA-GÓWNO]
;;; it is obvious how to fix that but as stated above, not worth it really.


(define (simplified form #;wrt metabinding)
  (match form
    [() '()]
    [('quote _) form]
    [('CONS h t) `(CONS ,(simplified h metabinding)
			,(simplified t metabinding))] ;; super-dirty.
    [('quasiquote qqe) `(,'quasiquote ,(qqexpr<-cons (simplified (cons<-qqexpr qqe)
								 metabinding)))]
    [(? symbol? s) (match (assoc-ref metabinding s)
		     [#f s]
		     [(? with-jokers?) s]
		     [val `(quote ,val)])] ;; sure about quote???
    [('APPLY . as) `(APPLY . ,(map (lambda (f) (simplified f metabinding)) as))]))

[e.g. (simplified '(APPLY f `(,x ,x) y) (meta-binding '(x . y) '(qwe ?) '()))
      ===> (APPLY f `(qwe qwe) y)]


(define (projection #;with situation #;from compendium)
  (filter-map (lambda ((pattern body))
		(and-let* ([mb (meta-binding pattern situation '())])
		  `(,(pattern-instance pattern mb) ,(simplified body mb))))
	      compendium))

[e.g. (equal? (projection '? apnd) apnd)]
[e.g. (equal? (projection '? test) test)]

[e.g. (projection '((apd) () ?) apnd) ===> [((('apd) () ys) ys)]]

[e.g. (projection '((apd) () (q w)) apnd) ===> [((('apd) () '(q w)) '(q w))]]

[e.g. (projection '((apd) ? (q w e)) apnd)
      ===> ([(('apd) () '(q w e)) '(q w e)]
	    [(('apd) (x . xs) '(q w e)) `(,x . ,(APPLY '(apd) xs '(q w e)))])]

[e.g. (projection '((apd) ? ?) apnd)
      ===> ([(('apd) () ys) ys]
	    [(('apd) (x . xs) ys) `(,x . ,(APPLY '(apd) xs ys))])]

[e.g. (projection '((LAM2) repetition) test)
      ===> ([(('LAM2) 'repetition) `(repetition repetition)])]

[e.g. (projection '((foldr) ? () ?) test)
      ===> ([(('foldr) _ '() ()) '()]
	    [(('foldr) op '() (x . xs)) (APPLY op x (APPLY '(foldr) op '() xs))])]

;;; it is worth noticing that the arity alone is often a valuable info:
[e.g. (projection '(? ? ?) test) ;; all binary functions:
      ===> ([(('map) f xs) (APPLY '(foldr) `(LAM1 ,f) () xs)]
	    [(('LAM1 f) h t) `(,(APPLY f h) . ,t)])]

[e.g. (projection '(? ?) test) ;; all unary functions:
      ===> ([(('LAM2) x) `(,x ,x)]
	    [(('test) xs) (APPLY '(map) '(LAM2) xs)])]


(define (applications #;in form)
  (match form
    [() '()]
    [('quote _) '()]
    [(? symbol?) '()]    
    [('CONS h t) (union (applications h) (applications t))]
    [('quasiquote qqe) (applications (cons<-qqexpr qqe))]
    [('APPLY . as) (union (apply union (map applications as)) `(,as))]))

(define (jokerized form)
  (match form
    [() '()]
    [('quote e) e]
    [(? symbol?) '?]
    [('quasiquote qqe) (let joqq ([e qqe])
			 (match e
			   [('unquote e) '?]
			   [(h . t) `(,(joqq h) . ,(joqq t))]
			   [_ e]))]
    [('APPLY . _) '?])) ;; NB now we can't do more here, but it's fine.

(define (following-situations projection)
  (map (lambda (ap) (map jokerized ap)) ;; because "application" is a list of forms
       (apply union (map (lambda ((_ form)) (applications form)) projection))))

[e.g. (following-situations (projection '((foldr) (LAM2) ? ?) test))
      ===> [((LAM2) ? ?)
	    ((foldr) (LAM2) ? ?)]]

[e.g. (following-situations (projection '((test) ?) test))
      ===> ([(map) (LAM2) ?])]

[e.g. (following-situations (projection '((map) (LAM2) ?) test))
      ===> ([(foldr) (LAM1 (LAM2)) () ?])]

[e.g. (following-situations (projection '[(foldr) (LAM1 (LAM2)) () ?] test))
      ===> ([(LAM1 (LAM2)) ? ?]
	    [(foldr) (LAM1 (LAM2)) () ?])]



(define (process-tree situation compendium)
  (let subtree ([ancestors '()]
		[situation situation])
    (let* ([prj (projection situation compendium)]
	   [ancestors* `(,situation . ,ancestors)]
	   [children (filter (lambda (s) (not (member? s ancestors*)))
			     (following-situations prj))])
      `(,situation ,prj ,(map (lambda (ch) (subtree ancestors* ch)) children)))))

(define (compendium<-tree tree)
  (and-let* ([(situation projection children) tree])
    (append (map (lambda ((pat frm)) `((,situation . ,pat) ,frm)) projection)
	    (append-map compendium<-tree children))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lolowa peniawka:

[e.g.
 (compendium<-tree (process-tree '((test) ?) test))
 ===>
 ([(((test) ?) ('test) xs)
   #;=> (APPLY '(map) '(LAM2) xs)]
  [(((map) (LAM2) ?) ('map) '(LAM2) xs)
   #;=> (APPLY '(foldr) `(LAM1 (LAM2)) () xs)]
  [(((foldr) (LAM1 (LAM2)) () ?) ('foldr) _ '() ())
   #;=> '()]
  [(((foldr) (LAM1 (LAM2)) () ?) ('foldr) '(LAM1 (LAM2)) '() (x . xs))
   #;=> (APPLY '(LAM1 (LAM2)) x (APPLY '(foldr) '(LAM1 (LAM2)) '() xs))]
  [(((LAM1 (LAM2)) ? ?) ('LAM1 '(LAM2)) h t)
   #;=> `(,(APPLY '(LAM2) h) unquote t)]
  [(((LAM2) ?) ('LAM2) x)
   #;=> `(,x ,x)]) ]

[e.g.
 (compendium<-tree (process-tree '((apd) (q w e) ?) apnd))
 ===>
 ([(((apd) (q w e) ?) ('apd) ('q . '(w e)) ys)
   #;=> `(q . ,(APPLY '(apd) '(w e) ys))]
  [(((apd) (w e) ?) ('apd) ('w . '(e)) ys)
   #;=> `(w . ,(APPLY '(apd) '(e) ys))]
  [(((apd) (e) ?) ('apd) ('e . '()) ys)
   #;=> `(e . ,(APPLY '(apd) '() ys))]
  [(((apd) () ?) ('apd) () ys)
   ys]) ]

[e.g. (compendium<-tree (process-tree '((apd) ? ?) apnd))
 ===>
 ([(((apd) ? ?) ('apd) ()       ys) #;=> ys]
  [(((apd) ? ?) ('apd) (x . xs) ys) #;=> `(,x . ,(APPLY '(apd) xs ys))]) ]

