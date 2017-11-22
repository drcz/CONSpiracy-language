;;; I don't always scheme, but when I do, I prefer (grand scheme).
(use-modules (grand scheme) (ice-9 pretty-print))

(define (_show e) (pretty-print e #:max-expr-width 150 #:width 150) #t)

(import (only (srfi srfi-1) alist-delete))
;;; he_he
(define reversed reverse) 
;;; we live in a nuclear age...
(define (atom? x) (not (pair? x)))
;;; ...and we like curried equalities too!
(define ((equals? x) y) (equal? x y))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; we work on classical lisp binary trees; McCarthy called them S-expressions,
;;; -- we call them cons-trees.
(define (cons-tree? x)
  (or (constant? x)
      (var? x)
      (and-let* ([('CONS hd tl) x]) (and (cons-tree? hd) (cons-tree? tl)))))

(define var? symbol?)

(define (constant? x)
  (or (null? x)
      (and-let* ([('quote s) x]) (atom? s))))
;;; for now we decide not to include numerals, even for natural numbers.
;;; nb there is no such thing as ``natural numbers'', which is rarely a problem,
;;; nobody actually needs them.

[e.g. (cons-tree? '())]
[e.g. (cons-tree? ''q)]
[e.g. (cons-tree? '(CONS x (CONS (CONS 'q 'w) ())))]

;;; it's funny that we use cons-trees to represent cons-trees; our representation
;;; of '(x . y) is (CONS 'x 'y), while the representation of this representation is
;;; (CONS 'CONS
;;;       (CONS (CONS 'quote (CONS 'x ()))
;;;             (CONS (CONS 'quote (CONS 'y ()))
;;;                   ())))
;;; -- might seem scary/stupid, BUT this way we never confuse 'CONS with CONS,
;;; which will be dead important when we start playing with Futamura projections
;;; and other ``metasystem'' meta-shits.
;;; also note that we only allow to quote symbols; therefore there is only one
;;; CONS ``syntactic'' and ``semantic'' -- or even better: ``there is no CONS''!


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; now the matter we will be transforming -- CONSequence compendia.
;;; CONSequence is a first order, patter-matching, denotative algorithmic language.
;;; to see example compendium (CONSpendium?!) search for serious-rich-compendium
;;; in the code below.

;;; NB we don't work on "programs", programs are good for washing machines and tv
;;; stations and theathres (and not so good for political parties, but since they
;;; are never "political" in Aristotelian sense, just screw them).

(define (compendium? x) (and (list? x) (every clause? x)))

(define (clause? x) (and-let* ([((? pattern?) (? form?)) x])))

(define pattern? cons-tree?)

;;; we only have one special form -- application.
(define (form? x)
  (or (cons-tree? x)
      (application? x)
      (and-let* ([('CONS hd tl) x]) (and (form? hd) (form? tl)))))

(define (application? x) (and-let* ([('APPLY as) x]) (form? as)))

[e.g. (form? '(CONS 'q 'w))]
[e.g. (form? '(CONS x (APPLY (CONS 'f (CONS x ())))))]

;;; excercise to the reader: can we always tell the difference between
;;; 'APPLY with APPLY?

;;; allright, admire how beautiful our representation for compendium is:
[e.g. (compendium? '( [(CONS 'concat (CONS () (CONS ys ())))
		       ys]
		      [(CONS 'concat (CONS (CONS x xs) (CONS ys ())))
		       (CONS x (APPLY (CONS 'concat (CONS xs (CONS ys ())))))] ))]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; hmmm... ok, MAYBE it is not THAT nice to read; therefore, just to avoid
;;; implementing the real thing, we will now implement some transformation magic
;;; to be able to work on fancier notation.

(define (rich-compendium? x) (and (list? x) (every rich-clause? x)))
(define (rich-clause? x) (and-let* ([((? rich-pattern?) (? rich-form?)) x])))

(define (rich-form? x)
  (or (constant? x)
      (var? x)
      (and-let* ([('quote _) x]))
      (and-let* ([('quasiquote qqe) x])
	(let proper-qqe? ([e qqe])
	  (match e
	    [() #t]
	    [(? symbol?) #t]
	    [('unquote e) (rich-form? e)]
	    [(h . t) (and (proper-qqe? h) (proper-qqe? t))]
	    [_ #f])))
      (and-let* ([('@ (? rich-form?)) x]))))

(define (rich-pattern? x)
  (or (and-let* ([('quote (? constant?)) x])) ;; TODO only constant -- sure?
      (var? x)
      (null? x)
      (and-let* ([(ph . pt) x])
	(and (rich-pattern? ph) (rich-pattern? pt)))))

[e.g. (rich-form? '`(,x . ,(@ `(apd ,xs ,ys))))]
[e.g. (rich-form? '`(hi there ,x))]
[e.g. (rich-pattern? '('if ('= x (y . ys)) c a))]

[e.g. (rich-compendium? '([('concat ()       ys) ys]
			  [('concat (x . xs) ys) `(,x . ,(@ `(concat ,xs ,ys)))]))]

;;; note that this ``rich'' notation is ambiquous, e.g. `(q . (w)), `(q w),
;;; '(q w) and '(q . (w)) all represent (CONS 'q (CONS 'w ())).


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

(define serious-rich-compendium
  '(
    [('foldr op e ()      ) e]
    [('foldr op e (x . xs)) (@ `(,op ,x ,(@ `(foldr ,op ,e ,xs))))]
    
    [('apd xs ys) (@ `(foldr cons ,ys ,xs))]
    [('cons h t) `(,h . ,t)] ;; NB defunctionalized higher-order function here!
    
    [('map f xs) (@ `(foldr (cons-f ,f) () ,xs))]
    [(('cons-f f) h t) `(,(@ `(,f ,h)) . ,t)] ;; NB a defunctionalized closure! 
    ))

[e.g. (rich-compendium? serious-rich-compendium)]
[e.g. (equal? serious-rich-compendium
	      (richcompendium<-compendium
	       (compendium<-richcompendium
		serious-rich-compendium)))]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ok, back to business.
;;; since ``there is no CONS'', we [mostly] care only about leaves of CONStrees:
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; embedding relation -- a partial order on constrees. useful.
(define (embedded? ct CT)
  (match CT
    [(? (equals? ct)) #t]
    [('CONS hd tl) (or (embedded? ct hd) (embedded? ct tl))]
    [_ #f]))

[e.g. (embedded? ''x ''x)]
[e.g. (embedded? ''x '(CONS 'x 'y))]
[e.g. (not (embedded? ''x ''y))]
[e.g. (not (embedded? ''x '(CONS 'y ())))]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NB all cons-trees (and therefore patterns), are forms in our representation.
(define (free-vars #;in form-or-pattern)
  (match form-or-pattern
    [(? constant?) '()]
    [(? var? v) `(,v)]
    [('CONS hd tl) (union (free-vars hd) (free-vars tl))]
    [('APPLY as) (free-vars as)]))

[e.g. (free-vars '(CONS x 'qwe)) ===> (x)]
[e.g. (free-vars '(CONS x (APPLY (CONS 'concat (CONS x (CONS y ())))))) ===> (y x)]

;;; sometimes we need to spawn a new variable.
;;; now this is just to make them look fancy. in CONSpiracy implementation
;;; we will rather use lists as variable names, e.g. (var x), (var x * *) etc.
;;; so that in case of metasystem mumbo-jumbo Buddha can recognize attempts
;;; to create indefinite number of variables, something something.
(define (fresh-var #;with prefix #;not-clashing-with reserved-vars)
  (define (new-var prefix)
    (string->symbol (string-append (symbol->string prefix) "*")))
  (let next ([prefix prefix])
    (if (member? prefix reserved-vars)
	(next (new-var prefix))
	prefix)))

[e.g. (fresh-var 'x '(x x*)) ===> x**]
[e.g. (fresh-var 'y '(x x*)) ===> y]


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; let's talk about bindings... these tiny fuckers represent mapping(s) from
;;; variables to something -- in our case to cons-trees.
(define (binding? x)
  (and (list? x)
       (every (lambda (p) (and-let* ([((? var?) . (? cons-tree?)) p]))) x)))

[e.g. (binding? '([x . 'qwe] [y . (CONS x xs)] [z . ()]))]
[e.g. (binding? '())]

;;; variables are called keys.
(define (keys binding) (map car binding))

;;; binding can be ``looked up''...
(define (value #;of binding #;for key)
  (match binding
    [() #f]
    [([(? (equals? key)) . val] . _) val]
    [(_ . binding) (value binding key)]))

[e.g. (value '([x . 'qwe] [y . (CONS x xs)] [z . ()]) 'x) ===> 'qwe]
[e.g. (value '([x . 'qwe] [y . (CONS x xs)] [z . ()]) 'y) ===> (CONS x xs)]
[e.g. (value '([x . 'qwe] [y . (CONS x xs)]) 'z) ===> #f]

;;; ...extended...
(define (extended binding #;with var constree)
  `([,var . ,constree] . ,(alist-delete var binding)))

[e.g. (extended '([x . 'qwe] [y . (CONS x xs)]) 'z '(CONS 'zzz x))
      ===> ([z . (CONS 'zzz x)] [x . 'qwe] [y . (CONS x xs)])]
[e.g. (extended '([x . 'qwe] [y . (CONS x xs)]) 'x '(CONS 'zzz x))
      ===> ([x . (CONS 'zzz x)] [y . (CONS x xs)])]

;;; ...and substituted into a form:
(define (substituted binding #;into form)
  ((vars-wise (lambda (v) (or (value binding v) v))) form))

[e.g. (substituted '([x . 'qwe] [y . (CONS x xs)])
		   '(CONS 'he_he (CONS (CONS x y) (CONS z ()))))
      ===> (CONS 'he_he (CONS (CONS 'qwe (CONS x xs)) (CONS z ())))]
;;; TODO more ``delicate'' and informative examples


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; instances, generalizations, whistle...

(define (whistle? descendant ancestor)
  (match `(,descendant ,ancestor)
    [(('APPLY as) ('APPLY as*)) (whistle? as as*)] ;; !!    
    [(e e) #t]
    [((? var?) (? var?)) #t]
    [(('CONS h t) ('CONS h* t*)) (or (and (whistle? h h*) (whistle? t t*))
				     (whistle? h ancestor)
				     (whistle? t ancestor))]
    [(('CONS h t) e) (or (whistle? e h) (whistle? e t))]
    [otherwise #f]))

(define (instance? descendant ancestor) ;;; TODO should suffice?
  (match `(,descendant ,ancestor)
    [(('APPLY as) ('APPLY as*)) (instance? as as*)]    
    [(_ (? var?)) #t]
    ;;; TODO: zapewne ('_ _) i (_ '_) to #t...
    [(e e) #t]
    [(('CONS h t) ('CONS h* t*)) (and (instance? h h*) (instance? t t*))]
    [_ #f]))

(define (generalized application #;such-that
		     descendant-application #;is-its-instance)
  (_show `(GEN ,(richform<-form application)
               ,(richform<-form descendant-application)))
  (and-let* ([('APPLY args) application]
             [('APPLY args*) descendant-application]
             [(gen-args . subst) (generalization args args*)])
    `(APPLY ,gen-args) #;`(LETs ,subst (APPLY ,gen-args))))

;;; TODO: ważne żeby poniższe sprawdzić czy dalij ma sens [józkejsy napisać]
(define (generalization #;of ctree #;wrt ctree* . substitution)
  (match `(,ctree ,ctree*)
    [(() ())
     `(() . ,substitution)]
    [((? var? v) (? var? v*))
     (let ([fresh (fresh-var v (keys substitution))])
       `(,fresh . ,(extended substitution fresh v)))]
    [((? var? v) _)
     `(,v . ,(extended substitution v v)) ;; ?! mosz tak?
     #;(let ([fresh (fresh-var v (keys substitution))])
       `(,fresh . ,(extended substitution fresh v)))]
    [(('quote e) ('quote e))
     `((quote ,e) . ,substitution)]
    [(('CONS h t) ('CONS h* t*))
     (and-let* ([(gen-h . subst*) (apply generalization h h* substitution)]
		[(gen-t . subst**) (apply generalization t t* subst*)])
       `((CONS ,gen-h ,gen-t) . ,subst**))]
    [(e e*)
     (let ([fresh (fresh-var 'g (keys substitution))])
       `(,fresh . ,(extended substitution fresh e)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the process tree...

(define (new-tree (pattern form) children)
  `(T (,pattern ,form) ,children))

(define (tree? x)
  (and-let* ([('T [(? pattern?) (? form?)] ts) x])
    (every tree? ts))) ;;; możnaby ostrzej, że ts puste ino jeśli form to nie ap.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ``driving'':

(define (sub-tree pattern form ancestors compendium)
  (_show `(st (anc.c. ,(length ancestors)) ,(richform<-form form)))
  (or [and (cons-tree? form)
           (new-tree `(,pattern ,form) '())]

      [and (any (lambda (anc) (#;equal? instance? form anc)) ancestors)
           (new-tree `(,pattern ,form) '())]

      [and-let* ([dejavu (find (lambda (anc) (whistle? form anc)) ancestors)])
        `(GENERALIZE ,dejavu #;s.t. ,form #;would-be-its-instance)]

      [let* ([futures (futures form compendium)]
             [ancestors* (if (> (length futures) 1)
                             `(,form . ,ancestors)
                             ancestors)])
        (let children ([pending futures]
                       [results '()])
          (match pending
            [()
             (and (not (null? results)) ;; a contradiction?
                  (new-tree `(,pattern ,form) (reverse results)))]
            [((pattern* form*) . pending*)
             (match (sub-tree pattern* form* ancestors* compendium)
               [('GENERALIZE whom #;wrt what)
                (if (equal? whom form) ;; start again...
                    (match (sub-tree pattern
                                     (generalized form #;wrt what)
                                     ancestors
                                     compendium)
                    ;;; children with less information but the form (application)
                    ;;; itself should remain untouched as otherwise we loose what
                    ;;; we forgot... this is because we don't have LET forms
                      [('T (pattern* form*) chs*) `(T (,pattern ,form) ,chs*)]
                      [some-non-tree-thing some-non-tree-thing])
                    `(GENERALIZE ,whom ,what))]
               [(? tree? subtree*)
                (children pending* `(,subtree* . ,results))]
               [#f #;#f ;;; TODO czemu to się pętliło poniższe skoro ma sens? ;)
                (children pending* results)])]))]))
  
"
(define (futures application compendium)
  (fold-left (lambda (projections (pattern form))
               (or (and-let* ([('APPLY situation) application]
                               [renaming (de-clashing-renaming pattern
                                                               (free-vars
                                                                situation))]
                               [pattern* (substituted renaming pattern)]
                               [form* (substituted renaming form)]
                               [binding (unifier pattern* situation)]
                               [pattern** (substituted binding pattern*)]
                               [form** (substituted binding form*)])
                      (and (not (member? pattern** (map first projections)))
                           `(,@projections (,pattern** ,form**))))
                   projections))
              '()
              compendium))
"

;;; futures of the future!
(define (futures application compendium)
  (fold-left (lambda (projections (pattern form))
               (or (and-let* ([('APPLY situation) application]
                               [renaming (de-clashing-renaming pattern
                                                               (free-vars
                                                                situation))]
                               [pattern* (substituted renaming pattern)]
                               [form* (substituted renaming form)]
                               [binding (unifier pattern* situation)]
                               [pattern** (substituted binding pattern*)]
                               [form** (substituted binding form*)])
                      (and (not (any (lambda (ptrn) (instance? pattern** ptrn))
                                     (map first projections)))
                           `(,@projections (,pattern** ,form**))))
                   projections))
              '()
              compendium))


(define (de-clashing-renaming form reserved-vars)
  (let* ([form-vars (free-vars form)]         
         [clashing (intersection reserved-vars form-vars)])
    (map (lambda (v) `[,v . ,(fresh-var v reserved-vars)]) clashing)))


(define (unification #;for form-a #;and form-b . binding)
;[pretty-print `(unf ,form-a ,form-b ,binding)]
  (match `(,form-a ,form-b)
    [('_ _) binding] ;; !
    [(_ '_) binding] ;; ! 
    [(x x) binding]
    [((? var? v) _) (match (value #;of binding #;for v)
                      [#f (and (not (embedded? v form-b)) ;; TODO: sure? <- YES?!
                               (extended binding v form-b))]
                      [form* (apply unification form* form-b binding)])]
    [(_ (? var?)) (apply unification form-b form-a binding)] ;; ``swap!''
    [((? constant? c) _) (and (equal? c form-b) binding)]
    [(('CONS h-a t-a) ('CONS h-b t-b))
     (and-let* ([binding* (apply unification h-a h-b binding)])
       (apply unification t-a t-b binding*))]
    [otherwise #f])) ;; !

;;; now mind we want unifier to be a binding such that when substituted
;;; to form-a and form-b yields the same new form, i.e.
;;;  (let ([u (unifier form-a form-b)])
;;;   (equal? (substituted u form-a) (substituted u form-b)))

(define (cycle-free-binding binding)
  (fold-right (lambda ((k . v) binding)
                (if (and (var? v) (member? `(,v . ,k) binding))
                    binding
                    `((,k . ,v) . ,binding)))
              '()
              binding))

;;; actualy the process in unifier always converges, but...
(define (greedily-but-not-oscillating op init . history) ;; :D
  (if (member? init history)
      init
      (apply greedily-but-not-oscillating op (op init) `(,init . ,history))))

(define (unifier form-a form-b)
  (and-let* ([binding (unification form-a form-b)])
    (greedily-but-not-oscillating
     (lambda (bnd)
         (cycle-free-binding
        (map (lambda ((k . v))
               `(,k . ,(substituted binding v)))
             bnd)))
     binding)))


"
(unifier (form<-richform '`(g ,a ,b))
         (form<-richform '('g (x . xs) ys)))

(unifier (form<-richform '`(g (,a . ,as) ,b))
         (form<-richform '('g xs ys)))

(unifier '(CONS 'concat (CONS (CONS x xs*) (CONS ys ())))
         '(CONS 'concat (CONS xs (CONS ys ()))))
"                         


"
(define concat-cmpd
  (compendium<-richcompendium
   '([('concat ()       ys) ys]
     [('concat (x . xs) ys) `(,x . ,(@ `(concat ,xs ,ys)))])))

[pretty-print (richcompendium<-compendium
       (futures (form<-richform '(@ `(concat ,xs ,ys)))
                concat-cmpd))]

[pretty-print (richcompendium<-compendium
       (futures (form<-richform '(@ `(concat (q w e) ,ys)))
                concat-cmpd))]

[pretty-print (richcompendium<-compendium
       (futures (form<-richform '(@ `(concat (,xs . ,xs) ,ys)))
                concat-cmpd))]
"
;;; wszo okejo... :O



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ``building''

#;(define (compendium<-tree tree)
  (match tree
    [() '()]
    [('T (p f) chs)
     `([,p ,f] . ,(append-map compendium<-tree chs))]))
     
;;; that was easy!
;;;  ...and here's a bit more "organized" [?!] version:
(define (compendium<-tree tree)
  (match tree
    [() '()]
    [('T (p f) chs)
     `([,p ,f] . ,(let prc-chs ([chs chs] [left '()])
                    (match chs
                      [()
                       (append-map compendium<-tree left)]
                      [(('T (p f) c*) . chs)
                       `((,p ,f) . ,(prc-chs chs (append c* left)))])))]))

#;(define (compendium<-tree tree)
  (match tree
    [() '()]
    [('T (p f) chs)
     `([,p ,f] . ,(let prc-chs ([chs chs] [left '()])
                    (match chs
                      [()
                       (if (null? left) '() (prc-chs left '()))]
                      [(('T (p f) c*) . chs)
                       `((,p ,f) . ,(prc-chs chs (append c* left)))])))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; transitions compression???

(define (new-tree* (pattern form) children)
  (or (and (= (length children) 1)
           (and-let* ([('APPLY situation) form]
                      [('T (ch-patt ch-form) chs) (first children)]
                      ;[_elo_ (_show `(CHLDRN: ,children))]
                      [binding (unifier ch-patt situation)]
                      ;[_elo_ (_show `(BND ,(richform<-form ch-patt) x ,(richform<-form situation) => ,binding))]
                      ;[_elo_ (_show `(FRM* ,(richform<-form (substituted binding ch-form))))]
                      [pattern* (substituted binding pattern)]
                      [form* (substituted binding ch-form)]) ;; sic!, ch-form
             `(T (,pattern* ,form*) ,chs)))
      `(T (,pattern ,form) ,children)))

(define (compress-transitions tree)
  (match tree
    [() '()]
    [('T pat-frm chldrn)
     (let ([tree* (new-tree* pat-frm chldrn)])
       (if (not (equal? tree tree*))
           (compress-transitions tree*)
           `(T ,pat-frm ,(map compress-transitions chldrn))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; et voila?!

(define conc-cmpd
  (compendium<-richcompendium
   '([('concat ()       ys k) (@ `(,k ,ys))]
     [('concat (x . xs) ys k) (@ `(concat ,xs ,ys (Ak ,x ,k)))]
     [('id x) x]
     [(('Ak x k) v) (@ `(,k (,x . ,v)))])))


"
(_show
 (richcompendium<-compendium
  (compendium<-tree
   (compress-transitions
    (sub-tree (pattern<-richpattern '('DUPA us))
              (form<-richform '(@ `(concat ,us (q w e) id)))
              '()
              conc-cmpd)))))

(pretty-print '-------------------)


(_show
 (richcompendium<-compendium
  (compendium<-tree
   (compress-transitions
    (sub-tree (pattern<-richpattern '('DUPA us))
              (form<-richform '(@ `(concat (q w e) ,us id)))
              '()
              conc-cmpd)))))

(pretty-print '-------------------)

(_show
 (richcompendium<-compendium
  (compendium<-tree
   (compress-transitions
    (sub-tree (pattern<-richpattern '('DUPA us))
              (form<-richform '(@ `(concat ,us (q w e) id)))
              '()
              conc-cmpd)))))

(pretty-print '-------------------)

(_show
 (richcompendium<-compendium
  (compendium<-tree
   (compress-transitions
    (sub-tree (pattern<-richpattern '('DUPA k))
              (form<-richform '(@ `(concat (q w e) (a s d) ,k)))
              '()
              conc-cmpd)))))

(pretty-print '-------------------)


"
"
(pretty-print 
 (richcompendium<-compendium
  (compendium<-tree
   (sub-tree (pattern<-richpattern '('DUPA us zs))
             (form<-richform '(@ `(concat ,zs ,us id)))
             '()
             conc-cmpd))))

(pretty-print 
 (richcompendium<-compendium
  (compendium<-tree
   (sub-tree (pattern<-richpattern '('DUPA us zs))
             (form<-richform '(@ `(concat (q w . ,zs) ,us id)))
             '()
             conc-cmpd))))
"

(define test2
  (compendium<-richcompendium
   '( [('match p s) (@ `(m ,p ,s ,p ,s))]
      
      [('m ()       ss op os) 'TRUE]
      [('m (p . pp) ss op os) (@ `(x ,p ,pp ,ss ,op ,os))]

      [('x p pp ()       op os) 'FALSE]
      [('x p pp (p . ss) op os) (@ `(m ,pp ,ss ,op ,os))]
      [('x p pp (q . ss) op os) (@ `(n ,op ,os))]

      [('n op (s . ss)) (@ `(m ,op ,ss ,op ,ss))] )))

"
(_show
 (richcompendium<-compendium
  (futures (form<-richform '(@ `(m (A A B) (A ,q . ,ss*) (A A B) (A ,q . ,ss*))))
           test2)))
"
(_show
 (richcompendium<-compendium
  (futures (form<-richform '(@ `(x A (A B) (,q . ,ss*) (A A B) (,q . ,ss*))))
           test2)))



(define (print-compendium c) ;;; niepoczebne w sumje
  (match c
    [() #t] 
    [((p f) . c) 
     (begin (_show `[,p ,f])
            #;(newline) 
            (print-compendium c))]))

(print-compendium
 (delete-duplicates 
  (richcompendium<-compendium
   (compendium<-tree
    (compress-transitions
     (sub-tree (pattern<-richpattern '('DUPA ss))
               (form<-richform '(@ `(match (A A B) ,ss)))
               '()
               test2))))))

#;(pretty-print
(futures (form<-richform '(@ `(x ,p ,pp (,a . ,b) ,xx ,yy)))
         test2))

"
(define kupka
(unifier (form<-richform '('x p pp (p . ss*) op os))
         (form<-richform '`(x A (A B) ,ss (A A B) ,ss))))

(richform<-form 
 (substituted
  kupka
  (substituted
   kupka
   (substituted
    kupka
    (form<-richform '('x p pp (p . ss*) op os))))))


;jedna kupka:
'`(x A (A B) (A . ,ss*) (A A B) ,ss)
;dwie kupki:
`(x A (A B) (A . ,ss*) (A A B) (,p . ,ss*))
;trzy kupki:
`(x A (A B) (A . ,ss*) (A A B) (A . ,ss*))
;;; elegancko.
"

;;;;;;;;;;;;;;;;; total madness

(define drc-machine
  (compendium<-richcompendium
   '[
#;(-- the DRC machine in algorithmic language CONSequence --)

#;( -- because cats are cute -- )
[('cat ()       ys K) (@ `(,K ,ys))]
[('cat (x . xs) ys K) (@ `(cat ,xs ,ys (catK ,x ,K)))]
[(('catK x k) v) (@ `(,k (,x . ,v)))]

#;( -- ops on dictionary (the environment) -- )
[('name k v dict K) (@ `(,K ([,k . ,v] . ,dict)))]
#;[('name k v dict K) (@ `(cat ,dict ([,k . ,v]) ,K))] ;; horror.

[('forget k ([k . v] . dict)  K) (@ `(,K ,dict))]
[('forget k ([k* . v] . dict) K) (@ `(forget ,k ,dict (forgetK [,k* . ,v] ,K)))]
[(('forgetK [k . v] K) dict) (@ `(,K ([,k . ,v] . ,dict)))]

[('lookup k ([k . v] . dict) K) (@ `(,K ,v))]
[('lookup k ([q . v] . dict) K) (@ `(lookup ,k ,dict ,K))]

#;( -- the machine proper -- )
[('run program inputs) (@ `(step* () ,inputs ,program))]

#;(- memory/store aka operating D -)
[('step* D (e . R) (['NAME n]   . C)) (@ `(name ,n ,e ,D (step*DK ,R ,C)))]
[('step* D R       (['FORGET n] . C)) (@ `(forget ,n ,D (step*DK ,R ,C)))]
[('step* D R       (['LOOKUP n] . C)) (@ `(lookup ,n ,D (step*RK ,D ,R ,C)))]

#;(- constants and operators aka operating on R -)
[('step* D R (['CONST e] . C)) (@ `(step* ,D (,e . ,R) ,C))]
[('step* D R (['PROC p]  . C)) (@ `(step* ,D (,p . ,R) ,C))]

[('step* D (h t . R)     (['CONS] . C)) (@ `(step* ,D ((,h . ,t) . ,R) ,C))]
[('step* D ((h . t) . R) (['CAR] . C)) (@ `(step* ,D (,h . ,R) ,C))]
[('step* D ((h . t) . R) (['CDR] . C)) (@ `(step* ,D (,t . ,R) ,C))]

[('step* D (e e . R)     (['EQ?] . C)) (@ `(step* ,D (T  . ,R) ,C))]
[('step* D (e f . R)     (['EQ?] . C)) (@ `(step* ,D (() . ,R) ,C))]
[('step* D ((h . t) . R) (['ATOM?] . C)) (@ `(step* ,D (() . ,R) ,C))]
[('step* D (a       . R) (['ATOM?] . C)) (@ `(step* ,D (T  . ,R) ,C))]

#;(- control flow aka operating on C -)
[('step* D (() . R) (['SELECT p p*] . C)) (@ `(cat ,p* ,C (step*CK ,D ,R)))]
[('step* D (t  . R) (['SELECT p p*] . C)) (@ `(cat ,p ,C (step*CK ,D ,R)))]
[('step* D (p . R) (['APPLY] . C)) (@ `(cat ,p ,C (step*CK ,D ,R)))]

#;(- the three little continuations -)
[(('step*DK R C) D) (@ `(step* ,D ,R ,C))]
[(('step*RK D R C) r) (@ `(step* ,D (,r . ,R) ,C))]
[(('step*CK D R) C) (@ `(step* ,D ,R ,C))]

#;(- halting? not a problem! -)
[('step* D (e . R) ()) e]
     ]))

(define drc-program-apd
  '([PROC ([NAME xs]
           [NAME ys]
           [LOOKUP xs]
           [CONST ()]
           [EQ?]
           [SELECT ([LOOKUP ys])
                   ([LOOKUP ys]
                    [LOOKUP xs]
                    [CDR]
                    [LOOKUP concat]
                    [APPLY]
                    [LOOKUP xs]
                    [CAR]
                    [CONS])]
           [FORGET ys]
           [FORGET xs])]
    [NAME concat]
    [LOOKUP concat]
    [APPLY]))
    

(define drc-machine-run
  (form<-richform
   `(@ (,'quasiquote (run ,drc-program-apd ((q w e) #;(,'unquote as) (a s d)))))))

;;; doobrze!

(pretty-print '-------------------------------------------------------------)
(pretty-print '--tera-bedzie-hardkor----------------------------------------)

(print-compendium
; (delete-duplicates 
  (richcompendium<-compendium
   (compendium<-tree
    (compress-transitions
     (sub-tree (pattern<-richpattern '('DUPA as))
               drc-machine-run
               '()
               drc-machine)))))

"
(print-compendium
 (richcompendium<-compendium
  (futures
   (form<-richform
    '(@ `((,g ,g* ,v . ,g**) ,v*))
    #;'(@ `(step* ((ys a s d)
                 (xs q w e)
                 (concat
                   (NAME xs)
                   (NAME ys)
                   (LOOKUP xs)
                   (CONST ())
                   (EQ?)
                   (SELECT ((LOOKUP ys)) ((LOOKUP ys) (LOOKUP xs) (CDR) (LOOKUP concat) (APPLY) (LOOKUP xs) (CAR) (CONS)))
                   (FORGET ys)
                   (FORGET xs)))
                (())
                ((SELECT ((LOOKUP ys)) ((LOOKUP ys) (LOOKUP xs) (CDR) (LOOKUP concat) (APPLY) (LOOKUP xs) (CAR) (CONS))) (FORGET ys) (FORGET xs)))))
   drc-machine)))
"
