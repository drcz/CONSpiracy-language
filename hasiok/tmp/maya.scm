;;; all of this is maya.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-modules (grand scheme))
(define (pair xs ys) (map cons xs ys)) ;; alternative to grand zip...

(define (map-find f xs) ;; disgusting!
  (match xs
    [() #f]
    [(x . xs) (match (f x)
                [#f (map-find f xs)]
                [val val])]))

[e.g. (map-find (lambda (x) (and (< x 0) `(neg! ,x))) '(0 1 2 -3))
      ===> (neg! -3)]

;;; ^-- not sure i'll use it.


;;; working with compex quote forms is annoying and unnecessary.
;;; they create various problems with quoting and unquoting. fuck them.
(define (cons<-quote x) ;;; ``the residual code for quote-form''
  (let ([('quote e) x])
    (let c<-q ((e e))
      (match e
        [() '()]
        [(? symbol?) `(quote ,e)]
        [(h . t) `(cons ,(c<-q h) ,(c<-q t))]))))

[e.g. (cons<-quote ''qwe) ===> 'qwe]
[e.g. (cons<-quote ''(a b c)) ===> (cons 'a (cons 'b (cons 'c ())))]
[e.g. (cons<-quote ''((a . b) c)) ===> (cons (cons 'a 'b) (cons 'c ()))]


(define (var? x) (and (symbol? x) (not (mvar? x))))

(define (mvar? x) (and (symbol? x)
                       (eq? (first (string->list (symbol->string x))) #\?)))

;;; a ground expression is one with no metavariables.
;;; since we're working with residual code, not only flat expressions,
;;; if there is an application "left" there must be a metavariable
;;; -- cf last e.g. form below.
(define (ground? x)
  (match x
    [() #t]
    [('quote _) #t]
    [('cons h t) (and (ground? h) (ground? t))]
    [_ #f]))

[e.g. (ground? '(cons 'a 'b))]
[e.g. (not (ground? '(cons 'a ?1)))]
[e.g. (not (ground? '?1))]
[e.g. (not (ground? '(cons 'a (car ?1))))]

;;; we make an assuption that this could not happen:
[e.g. (not (ground? '(car (cons 'a 'b))))]
;;; because the expression would be immediately reduced to 'a alone.
;;; however keep this in mind.


(define (lookup var env)
  (match env
    [() #f]
    [([var* . val*] . env*) (if (eq? var var*) val* (lookup var env*))]))


(define (expr-metavars expr)
  (match expr
    [() '()]
    [('quote _) '()]
    [(? var?) '()]
    [(? mvar? m) `(,m)]
    [('cons h t) (union (expr-metavars h) (expr-metavars t))]
    [('car f) (expr-metavars f)]
    [('cdr f) (expr-metavars f)]
    [('eq? f f*) (union (expr-metavars f) (expr-metavars f*))]
    [('atom? f) (expr-metavars f)]
    [('nlet _ ((mvars _) ...) f) (union mvars (expr-metavars f))] ;; ?! TODO
    [('goto _ . fs) (apply union (map expr-metavars fs))]
    [('if . fs) (apply union (map expr-metavars fs))]))

[e.g. (expr-metavars '(cons (car xs)
                            (cons ?1
                                  (if (eq? ?2 ?3) () (goto 3 ?2 (car ?1))))))
      ===> (?2 ?3 ?1)]

;;; i am not sure we want this:
[e.g. (expr-metavars '(cons 'a (nlet 23 ((?1 ?1) (?2 'q))
                                     (cons ?2 (goto 23 (cdr ?1) ?2)))))
      ===> (?1 ?2)]
;;; ie maybe it should be just ?1 ... ??? TODO


;;; it might be wiser to keep list of metavars in imagine, as we might
;;; forget about some of these... but who know. TODO
(define (metavars #;in env)
  (apply union (map (lambda ((k . v)) (expr-metavars v)) env)))

[e.g. (metavars '([xs . ?1] [ys . (cons 'q (cons 'w ?2))]))
      ===> (?2 ?1)]


;;; entries in history need names unique only wrt to their branch really.
(define (history+ form env history)
  (let* ([used-names (map (lambda ((name _ _)) name) history)]
         [new-name (if (null? used-names) 0 (1+ (apply max used-names)))])
    `([,new-name ,form ,env] . ,history)))


;;; (...)
;;; this one works on pairs of expressions
(define (mvars-mapping older younger . mapping)
  (match `(,older ,younger)
    [(() _)
     mapping]
    [((? mvar? mv) e)
     `([,mv . ,e] . ,mapping)]
    [((op x) (op x*)) (apply mvars-mapping x x* mapping)]
    [((op h t) (op h* t*))
     (and-let* ([mapping* (apply mvars-mapping h h* mapping)])
       (apply mvars-mapping t t* mapping*))]
    [(e e) mapping]
    [_ #f]))

[e.g. (mvars-mapping '(cons ?1 ?2) '(cons (cons 'q ?1) ?2))
      ===> ([?2 . ?2] [?1 . (cons 'q ?1)])]


;;; TODO: make deeper comparison!! -> done but now avoid inconsistent ones
;;; [if they are possible at all... -- meaning mvars-mapping MIGHT happen
;;; to be inconsistent between consecutive (k.v) pairs...
(define ((instance? (name form env)) (name* form* env*))
  (and (equal? form form*)
       (every (lambda ((k . v) (k* . v*))
                (and (eq? k k*) ;;; below it should be even stronger
                     (mvars-mapping v* v)))
              env env*)))

[e.g. ((instance? '(1
                    (if (= xs ()) ys (cons (car xs) (apd (cdr xs) ys)))
                    ([xs . (cons 'q ?3)] [ys . ?1])))
       '(3
         (if (= xs ()) ys (cons (car xs) (apd (cdr xs) ys)))
         ([xs . ?3] [ys . ?1])))]

[e.g. ((instance? '(1
                    (if (= xs ()) ys (cons (car xs) (apd (cdr xs) ys)))
                    ([xs . (cons 'q ())] [ys . ?1])))
       '(3
         (if (= xs ()) ys (cons (car xs) (apd (cdr xs) ys)))
         ([xs . 'q] [ys . ?1]))) ===> #f]

;;; compute "rename and goto" thingie.
;;; i am really not sure this will always work, we're just experimenting...
;;; env* <- ([x . ?1] [y . (cons 'a ?2)])
;;;  env <- ([x . (cons 'q ?1)] [y . (cons 'a ?2)])
;;; would yield ([?1 (cons 'q ?1)] [?2 ?2]).

(define (reorder mapping #;wrt keys)
  (match keys
    [() '()]
    [(k . keys) `([,k . ,(lookup k mapping)] . ,(reorder mapping keys))]))

[e.g. (reorder '([x3 . x3] [x1 . (cons 'a 'b)] [x2 . 'qwe]) '(x1 x2 x3))
      ===> ([x1 . (cons 'a 'b)] [x2 . 'qwe] [x3 . x3])]


(define (goto name env env*) ;;; env is "younger", ie is an instance of env*.
  (let* ([younger-vals (map cdr env)]
         [older-vals (map cdr env*)]
         ;;; optimistically assuming below one is consistent.
         [mapping (apply append (map mvars-mapping older-vals younger-vals))])
    `(goto ,name . ,(map cdr (reorder mapping #;wrt (metavars env*))))))

[e.g. (goto 23
            '([xs . (cons 'q ?1)] [ys . ?2])
            '([xs . ?1] [ys . ?2]))
      ===> (goto 23 ?2 (cons 'q ?1))]


(define (homeo-embedded? older #;in younger)
  (match `(,older ,younger)
    [(e e) #t]
    [((? mvar?) _) #t]
    [((op . xs) (op . ys))
     (or (any (lambda (y) (homeo-embedded? older y)) ys)
         (every (lambda (x y) (homeo-embedded? x y)) xs ys))]
    [(_ (op . xs))
     (any (lambda (x) (homeo-embedded? older x)) xs)]
    [_ #f]))

[e.g. (homeo-embedded? '?1 '(cons 'q ?1))]
[e.g. (not (homeo-embedded? '(cons ?1 'q) '(cons 'q ?1)))]
[e.g. (homeo-embedded? '(car ?1) '(cons (car ?1) ?2))]
[e.g. (not (homeo-embedded? '(car ?1) '(cdr ?1)))]
[e.g. (homeo-embedded? '(eq? ?1 ?2) '(eq? (car ?1) ?2))]
;;; mhm...

(define ((whistle? (_ form env)) (_ form* env*))
  (and (equal? form form*)
       (every (lambda ((k . v) (k* . v*))
                (and (eq? k k*) (homeo-embedded? v v*)))
              env env*)))

[e.g. ((whistle? '(2
                   (if (eq? xs ()) ys (cons (car xs) (apd (cdr xs) ys)))
                   ([xs . ?1] [ys . '(q w e)])))
       '(1
         (if (eq? xs ()) ys (cons (car xs) (apd (cdr xs) ys)))
         ([xs . (cdr ?1)] [ys . '(q w e)])))]


(define (fresh-mvar #;wrt used-mvars)
  (gensym '?)) ;;; TMP ;)

(define (expression-generalization #;of older #;st younger #;is-its-instance)
  (let ([mvars-in-use (metavars older)])
    (let gen ([older older]
              [younger younger])
      (match `(,older ,younger)
        [(e e) e]
        [((op . xs) (op . ys)) `(,op . ,(map gen xs ys))]
        [(_ _) (fresh-mvar mvars-in-use)]))))


(define (generalized nlet env env*)
  (let* ([('nlet num bnd body) nlet]
         [env* (reorder env* (map car env))] ;; JUST IN CASE
         [gen-env (map (lambda ((k . v) (k . v*))
                         `(,k . ,(expression-generalization v v*)))
                       env env*)]
         [new-mvars (metavars gen-env)] ;;?
         [new-bnd (apply append (map (lambda ((k . v) (k . v*))
                                       (mvars-mapping v v*))
                                     env env*))]
         ;;; todo check new-bnd for consistence...
         ;;; TODO!! we need to replace expressions for new mvars in body!!!!
         [new-nlet `(nlet ,num ,new-bnd ,body)])
    new-nlet))



;;; for eq? -- obviously sometimes disequality can be established for non-grounds.
(define (not-unifiable? x y) ;;; TODO more, perhaps [negated] unifier of budda?
  (match `(,x ,y)           ;;; at least embedded? as it's smart yet simple.
    [(e e) #f]
    [((? mvar?) _) #f]
    [(_ (? mvar?)) #f]
    [(('cons h t) ('cons h* t*)) (or (not-unifiable? h h*) (not-unifiable? t t*))]
    [(('cons h t) _) #t]
    [(_ ('cons h t)) #t]
    [_ #f]))

[e.g. (not-unifiable? '(cons 'a 'b) '())]
[e.g. (not-unifiable? '(cons 'c ()) '(cons 'c (cons 'a ?1)))]
[e.g. (not (not-unifiable? '(cons 'c ?1) '?2))]


;;; at the heart of it all:
(define (imagine form env history prog)
;  [pretty-print `(IMAGINE ,form ,env (history = ,history))]
  (match form
    [() '()]
    [(? var? v) (lookup v env)]
    [(? mvar? mv) mv]
    [('quote _) form] ;; preserve the quote!
    [('if p c a)
     (let* ([history* (history+ form env history)]
            [me (first history*)] ;; shitty, but...
            [(my-name _ _) me]
            [my-metavars (metavars env)]
            [my-mbinding (zip my-metavars my-metavars)])
       (match (find (instance? me) history)
         [(name* form* env*) (goto name* env env*)]
         [#f
          (match #f ;(find (whistle? me) history)
            ;[(name* form* env*) ...]
            [#f
             (match (imagine p env history* prog)
               [() (imagine a env history #;sic! prog)]
               [(? ground?) (imagine c env history #;sic! prog)]
               [form* `(nlet ,my-name ,my-mbinding
                             (if ,form*
                                 ,(imagine c env history* prog)
                                 ,(imagine a env history* prog)))])])]))]
    [(f . xs) 
     (match `(,f . ,(map (lambda (form*) (imagine form* env history prog)) xs))
       [('eq? x x) ''T]
       [('eq? (? ground?) (? ground?)) '()]
       [('eq? x y) (if (not-unifiable? x y) '() `(eq? ,x ,y))] ;; !
       [('atom? ()) ''T]
       [('atom? ('quote _)) ''T]
       [('atom? ('cons _ _)) '()]
       [('atom? x) `(atom? x)]
       [('car ('cons x _)) x]
       [('car x) `(car ,x)]
       [('cdr ('cons _ x)) x]
       [('cdr x) `(cdr ,x)]
       [('cons h t) `(cons ,h ,t)]
       [(f . vals) (and-let* ([(vars body) (lookup f prog)]
                              [env* (pair vars vals)])
                     (imagine body env* history prog))])]))


[e.g. (imagine '(dbl ?1) '() '() '([dbl (x) (cons x x)]))
      ===> (cons ?1 ?1)]

(define prg1
  '([apd (xs ys) (if (eq? xs ()) ys (cons (car xs) (apd (cdr xs) ys)))]))

[pretty-print (imagine '(apd (cons 'q (cons 'w (cons 'e ()))) ?1) '() '() prg1)]

[newline][newline][pretty-print '(testin simple instance-caused hatin)]

[pretty-print (imagine '(apd ?1 (cons 'q (cons 'w (cons 'e ())))) '() '() prg1)]

[newline][pretty-print '(testin simple instance-caused hatin pt2)]

[pretty-print (imagine '(apd ?1 ?2) '() '() prg1)]


[newline][pretty-print '(mrrr testin...)]
(define prg2
  '([apd (xs ys) (if (eq? xs ()) ys (cons (car xs) (apd (cdr xs) ys)))]
    [huh (xs) (apd (mapd xs) xs)]
    [dbl (x) (cons x x)]
    [mapd (xs) (if (eq? xs ()) () (cons (dbl (car xs)) (mapd (cdr xs))))]))

[pretty-print (imagine '(mapd (cons 'a (cons 'b (cons 'c ())))) '() '() prg2)]

[newline][pretty-print '(mrrr testin...!!)]
[pretty-print (imagine '(mapd ?1) '() '() prg2)]

[newline][pretty-print '(mrrr testin...!!!)]
[pretty-print (imagine '(cons 'zoba-to (mapd (cons 'a (cons 'b ?1)))) '() '() prg2)]


[newline][pretty-print '(mrrr testin...!!!!!!!!)]
[pretty-print (imagine '(huh (cons ?1 (cons ?2 ()))) '() '() prg2)]

[newline][pretty-print '(mrrr testin...!!!!!!!!!!!!)]
;;; FINALLY a case requiring generalization!
;[pretty-print (imagine '(huh (cons ?1 (cons ?2 ?3))) '() '() prg2)]

;;; this will make a lot of sense, if we see (nlet ...) and then (cdr (nlet ...))
;;; then it's obviously the case we want to bind this (nlet ...) to some fresh
;;; [meta]variable and repeat the imaginative process.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
