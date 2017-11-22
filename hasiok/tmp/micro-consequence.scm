(use-modules (grand scheme) (ice-9 pretty-print))

;;; semantics: ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (run app compendium)
  (richform<-form (value (form<-richform app)
                         (compendium<-richcompendium compendium))))
             
(define (value expression #;wrt compendium)
  [pretty-print `(v ,expression)]
  (match expression
    [(? constant?) expression]
    [('CONS h t) `(CONS ,(value h compendium) ,(value t compendium))]
    [('APPLY as)
     (let ([args (value as compendium)])
       (let first-match ([clauses compendium])
         (match clauses
           [() 'MISMATCH-ERROR]
           [((pattern form) . clauses*)
            (match (matching pattern args)
              [#f (first-match clauses*)]
              [binding (value (substituted binding form)
                              compendium)])])))]))

(define (matching pattern form . binding)
  (match pattern
    ['_ binding]
    [(? constant?) (and (equal? form pattern) binding)]
    [(? var? s) (match (assoc-ref binding s)
                  [#f `([,s . ,form] . ,binding)]
                  [form* (and (equal? form form*) binding)])]
    [('CONS h t) (and-let* ([('CONS h* t*) form]
                            [binding* (apply matching h h* binding)])
                   (apply matching t t* binding*))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; tmp syntax... ;;;
(define (atom? x) (not (pair? x)))
(define var? symbol?)

(define (cons-tree? x)
  (or (constant? x)
      (var? x)
      (and-let* ([('CONS hd tl) x]) (and (cons-tree? hd) (cons-tree? tl)))))

(define var? symbol?)

(define (constant? x)
  (or (null? x)
      (and-let* ([('quote s) x]) (atom? s))))

;;; tmp sugar ;;;
(define (form<-richform rich-form)
  (define (consized-q e)
    (match e
      [() '()]
      [(? symbol? s) `(quote ,s)]
      [(h . t) `(CONS ,(consized-q h) ,(consized-q t))]))
  (define (consized-qq qqe)
    (match qqe
      [() '()]
      [(? symbol? s) `(quote ,s)]
      [('unquote e) (form<-richform e)]
      [(h . t) `(CONS ,(consized-qq h) ,(consized-qq t))]))
  (match rich-form
    [(? constant? c) c]
    [(? var? v) v]
    [() '()]
    [('quote e) (consized-q e)]
    [('quasiquote qqe) (consized-qq qqe)]
    [('@ as) `(APPLY ,(form<-richform as))]
    [(h . t) `(CONS ,(form<-richform h) ,(form<-richform t))]))

(define (pattern<-richpattern rich-pattern)
  (match rich-pattern
    [() '()]
    [('quote e) (form<-richform rich-pattern)] ;; sic!
    [(? var? v) v]
    [(h . t) `(CONS ,(pattern<-richpattern h) ,(pattern<-richpattern t))]))

[e.g. (form<-richform '`(,x . ,(@ `(apd ,xs ,ys))))
      ===> (CONS x (APPLY (CONS 'apd (CONS xs (CONS ys ())))))]
[e.g.  (pattern<-richpattern '('apd-k (x . xs) ys k))
       ===> (CONS 'apd-k (CONS (CONS x xs) (CONS ys (CONS k ()))))]
       
;;; ...and back:
(define (richform<-form form)
  (define (qqf<-f form)    
    (match form
      [() '()]
      [(? var? v) `(,'unquote ,v)]
      [('quote e) e]
      [('CONS h t) `(,(qqf<-f h) . ,(qqf<-f t))]
      [('APPLY as) `(,'unquote (@ ,(richform<-form as)))]))
  (define (simple qqf)
    (match qqf
      [('quasiquote ('unquote e)) (simple e)]
      [(e . es) `(,(simple e) . ,(simple es))]
      [otherwise qqf]))
  (simple `(,'quasiquote ,(qqf<-f form))))

(define (richpattern<-pattern pattern)
  (match pattern
    [() '()]
    [('quote s) pattern]
    [(? var?) pattern]
    [('CONS h t) `(,(richpattern<-pattern h) . ,(richpattern<-pattern t))]))

[e.g. (richform<-form '(CONS x (APPLY (CONS 'apd (CONS xs (CONS ys ())))))) 
      ===> `(,x . ,(@ `(apd ,xs ,ys)))]
[e.g. (richpattern<-pattern '(CONS 'apd (CONS (CONS x xs) (CONS ys ()))))
      ===> ('apd (x . xs) ys)]

;;; NB (richform<-form (form<-richform rf)) is a nice ``normalizer'':
[e.g. (equal? (richform<-form (form<-richform '(@ '(apd (q w) (e r)))))
	      (richform<-form (form<-richform '(@ `(apd (q w) (e r)))))
	      (richform<-form (form<-richform '(@ `(apd ,'(q w) ,'(e r))))))]


;;; so now the encoding/decoding to/from CONSized CONSequence:
(define (compendium<-richcompendium richcompendium)
  (map (lambda ((pat form)) `(,(pattern<-richpattern pat) ,(form<-richform form)))
       richcompendium))

(define (richcompendium<-compendium compendium)
  (map (lambda ((pat form)) `(,(richpattern<-pattern pat) ,(richform<-form form)))
       compendium))

[e.g. (richcompendium<-compendium
       (compendium<-richcompendium
	'([('concat ()       ys) ys]
	  [('concat (x . xs) ys) `(,x . ,(@ `(concat ,xs ,ys)))])))
      ===> ((('concat () ys) ys)
	    (('concat (x . xs) ys)  `(,x . ,(@ `(concat ,xs ,ys))))) ]


;;; tmp substitutions ;;;

(define ((leaves-wise f) form)
  (match form
    [() '()]    
    [('CONS hd tl) `(CONS ,((leaves-wise f) hd) ,((leaves-wise f) tl))]
    [('APPLY as) `(APPLY ,((leaves-wise f) as))]
    [l (f l)]))

[e.g. ((leaves-wise (lambda (x) ''LOL)) '(CONS 'qwe (CONS x y)))
      ===> (CONS 'LOL (CONS 'LOL 'LOL))]

;;; and this one turns out to be extremelly useful:
(define (vars-wise f) (leaves-wise (lambda (l) (if (var? l) (f l) l))))

[e.g. ((vars-wise (lambda (x) ''ROTFL)) '(CONS 'qwe (CONS x y)))
      ===> (CONS 'qwe (CONS 'ROTFL 'ROTFL))]
;;; ...you get the idea.

(define (substituted binding #;into form)
  ((vars-wise (lambda (v) (or (assoc-ref binding v) v))) form))

[e.g. (substituted '([x . 'qwe] [y . (CONS x xs)])
		   '(CONS 'he_he (CONS (CONS x y) (CONS z ()))))
      ===> (CONS 'he_he (CONS (CONS 'qwe (CONS x xs)) (CONS z ())))]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; tmp run the shit
(let ([comp (read)]
      [app (read)])
  (pretty-print (run app comp)))



(define serious-rich-compendium
  '(
    [('foldr op e ()      ) e]
    [('foldr op e (x . xs)) (@ `(,op ,x ,(@ `(foldr ,op ,e ,xs))))]
    
    [('apd xs ys) (@ `(foldr cons ,ys ,xs))]
    [('cons h t) `(,h . ,t)] ;; NB defunctionalized higher-order function here!
    
    [('map f xs) (@ `(foldr (cons-f ,f) () ,xs))]
    [(('cons-f f) h t) `(,(@ `(,f ,h)) . ,t)] ;; NB a defunctionalized closure! 

    [('dbl x) `(,x ,x)]
    ))

(run '(@ `(apd (q w e) ,(@ `(map dbl (a s d))))) serious-rich-compendium)

