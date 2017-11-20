;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The [operational] semantics of CONSpiracy, aka the Thing.
;;; 2017.11.18-20, Alicante
(include "conspiracy-syntax.scm") ;; TODO: sure?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; "environments in general"...

(define binding? ;;; FYI
  (list-of (lambda ((k . v)) (and (identifier? k)
                             (or (closure? v)
                                 (expression? v))))))

(define (lookup binding #;for id)
  (match (assoc id binding)
    [#f '&UNBOUND]
    [(id . expr) expr]))

(import (only (srfi srfi-1) alist-delete)) ;; :)

(define (extended binding #;with id #;as expr)
  `([,id . ,expr] . ,(alist-delete id binding)))


;;; + internal representation of phi-forms with their enclosed bindings...
(define (closure? x)
  (and-let* ([('&CLOSURE ([(? pattern?) (? form?)] ...) (? binding?)) x])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the evaluator.

(define ((evaluator) #;of form
                     #;in-the-context-of defined 
                     #;on-error-applying error)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define (value form binding)
    (match form ;;; nb we assert desugared form here.

      [(? constant?) form]
      [(? closure?) form]

      [(? identifier? id) (match (lookup (append binding defined) id)
                            ['&UNBOUND (error `(unbound identifier ,id))]
                            [expr expr])]

      [('phi . cases) (let* ([vars-to-enclose (free-vars form)]
                           [binding* (filter (lambda ((k . _))
                                               (member? k vars-to-enclose))
                                             binding)])
                      `(&CLOSURE ,cases ,binding*))]

      [('quote e) e]

      [('quasiquote qqe) (let val-qq ([expr qqe])
                           (match expr
                             [('unquote e) (value e binding)]
                             [(h . t) `(,(val-qq h) . ,(val-qq t))]
                             [_ expr]))]

      [('if p c a) (if (value p binding)
                       (value c binding)
                       (value a binding))]

      [(rator . rands) (application (value rator binding)
                                    (if (list? rands)
                                        (map (lambda (r) (value r binding)) rands)
                                        (value rands binding))
                                    binding)]

      [_ (error `(unrecognized form ,form))]))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define (application rator rands local-binding)
    (match rator

      [(? primop?)
       (primop-application `(,rator . ,rands))]

      [('&CLOSURE cases enclosed-binding)
       (let ([match-bindings (append enclosed-binding local-binding)])
         (let first-matching ([cases cases])
           (match cases
             [()
              (error `(no matching in ,rator for ,rands))]
             [([pattern form] . cases*)
              (match (matching pattern rands match-bindings)
                [#f (first-matching cases*)]
                [binding (value form
                                (append binding enclosed-binding))])]
             [_ (error `(unrecognized closure cases ,cases))])))]

      [_ (error `(unrecognized application ,rator))]))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define (matching pattern form #;wrt match-bindings)
    (let matching ([pattern pattern]
                   [form form]
                   [binding '()])
      (match pattern

        ['_ binding]

        [(? constant?) (and (equal? form pattern) binding)]
        [('quote e) (and (equal? e form) binding)]
        
        [(? identifier? id)
         (match (lookup binding id)
           ['&UNBOUND (extended binding id form)]
           [form* (and (equal? form form*) binding)])]
        
        [('? guard) ;;; TODO appending binding below i'm not sure of...
         (and (value `(,guard ',form) (append binding match-bindings))
              binding)]
        
        [('? guard (? identifier? id)) ;; TODO as above.
         (match (lookup binding id)
           ['&UNBOUND
            (and (value `(,guard ',form) (append binding match-bindings))
                 (extended binding id form))]
           [form*
            (and (equal? form form*)
                 (value `(,guard ',form) (append binding match-bindings))
                 binding)])]
        
        [(p . ps) (and-let* ([(f . fs) form]
                             [binding* (matching p f binding)])
                    (matching ps fs binding*))]

        [_ (error `(unrecognized pattern ,pattern))])))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define (primop-application app)
    (match app

      [('&atom? x) (not (pair? x))]
      [('&atom? . _) (error `(&atom? expects 1 argument))]

      [('&str? x) (string? x)]
      [('&str? . _) (error `(&str? expects 1 argument))]

      [('&num? x) (numeral? x)]
      [('&num? . _) (error `(&num? expects 1 argument))]

      [('&tv? x) (truth-value? x)]
      [('&tv? . _) (error `(&tv? expects 1 argument))]

      [('&closure? x) (closure? x)]
      [('&closure? . _) (error `(&closure? expects 1 argument))]

      [('&eq? x x) #t]
      [('&eq? _ _) #f]
      [('&eq? . _) (error `(&eq? expects 2 arguments))]

      [('&lt? (? numeral? n) (? numeral? m)) (< n m)]
      [('&lt? . _) (error `(&lt? expects 2 numeral arguments))]

      [('&add (? numeral? n) (? numeral? m)) (+ n m)]
      [('&add . _) (error `(&add expects 2 numeral arguments))]

      [('&mul (? numeral? n) (? numeral? m)) (* n m)]
      [('&mul . _) (error `(&mul expects 2 numeral arguments))]

      [('&sub (? numeral? n) (? numeral? m)) (- n m)]
      [('&sub . _) (error `(&sub expects 2 numeral arguments))]

      [('&div (? numeral? n) 0) (error `(division by 0 is meaningless))]
      [('&div (? numeral? n) (? numeral? m)) (quotient n m)]
      [('&div . _) (error `(&div expects 2 numeral arguments))]

      [('&mod (? numeral? n) 0) (error `(modulo 0 is meaningless))]
      [('&mod (? numeral? n) (? numeral? m)) (modulo n m)]
      [('&mod . _) (error `(&mod expects 2 numeral arguments))]

      [('&strcat (? string? s) (? string? s*)) (string-append s s*)]
      [('&strcat . _) (error `(&strcat expects 2 string arguments))]

      [('&substr (? string? s) (? numeral? from))
       (substring s from)]
      [('&substr (? string? s) (? numeral? from) (? numeral? to))
       (substring s from to)]
      [('&substr . _)
       (error `(&substr expects 1 string followed by 1 or 2 numeral arguments))]

      [('&strlen (? string? s)) (string-length s)]
      [('&strlen . _) (error `(&strlen expects 1 string argument))]

      [('&display e) (begin (write e) (newline) e)] ;;; super-dirty ;)

      [_ (error `(unrecognized primitive application ,app))]))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; the notion of free variable...
  (define (free-vars form)
    (define (pattern-bound-vars pattern)
      (match pattern
        [(? identifier? id) `(,id)]
        [('quote _) '()]
        [('? _) '()]
        [('? _ id) `(,id)]
        [(p . ps) (union (pattern-bound-vars p) (pattern-bound-vars ps))]
        [_ '()]))

    (define (guards-free-vars pattern)
      (match pattern
        [(? identifier?) '()]
        [('quote _) '()]
        [('? guard . _) (free-vars guard)]
        [(p . ps) (union (guards-free-vars p) (guards-free-vars ps))]
        [_ '()]))

    (match form
      [(? identifier? id) `(,id)]
      
      [(? closure?) '()] ;; just think about it.

      [('phi . cases) (let fv-cases ([cases cases])
                      (match cases
                        [() '()]
                        [([pattern* form*] . cases*)
                         (union (difference (union (free-vars form*)
                                                   (guards-free-vars pattern*))
                                            (pattern-bound-vars pattern*))
                                (fv-cases cases*))]
                        [wtf? (error `(deformed phi form case ,wtf?))]))]

      [('quote _) '()]

      [('quasiquote qqe) (let fv-qq ([expr qqe])
                           (match expr
                             [('unquote e) (free-vars e)]
                             [(h . t) (union (fv-qq h) (fv-qq t))]
                             [_ '()]))]

      [('if p c a) (union (free-vars p) (free-vars c) (free-vars a))]

      [(f . (? list? args)) (apply union (map free-vars form))]
      [(f . a) (union (free-vars f) (free-vars a))]

      [_ '()]))

  #;(e.g. (free-vars '`(,x ,(f y (+ x y) z))) ===> (f y + z x))
  #;(e.g. (free-vars '(phi [(x) (* x x)])) ===> (*))
  #;(e.g. (free-vars '(phi [(x) (* x y)])) ===> (y *))

  #;(e.g. (free-vars '(phi [(x) (* x y)]
                       [(z y) (+ z y)]
                       [(z x) (f z x abc)])) ===> (+ abc f y *))

  #;(e.g. (free-vars '(phi [(? (phi [(x) (p? x)])) 'qwe])) ===> (p?))
  #;(e.g. (free-vars '(phi [((? p? x) (? q?)) `(,x ,xyz)])) ===> (p? q? xyz))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; one more thing, desugaring the syntax {perhaps not the best choice}
  (define (desugared form)
    (match form
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
       `(if ,(desugared f*) #f #t)]
 
      ;;; let's are just sugar for nested phi-forms (TODO: for now?)
      [('let bnds* f*)
       (fold-right (lambda ((pat frm*) bs) `((phi [(,pat) ,bs]) ,(desugared frm*)))
                   (desugared f*)
                   bnds*)]
      
      ;;; propagate desugaring into subforms...
      [(? phi-form?)
       (let* ([('phi . cases) form])
         `(phi . ,(map (lambda ((p* f*)) `(,(desugared-pattern p*)
                                    ,(desugared f*))) cases)))]

      [('if p* c* a*)
       `(if ,(desugared p*) ,(desugared c*) ,(desugared a*))]

      [('quasiquote qqe*)
       `(,'quasiquote ,(let desugared-qq ([expr qqe*])
                         (match expr
                           [('unquote e) `(,'unquote ,(desugared e))]
                           [(h . t) `(,(desugared-qq h) . ,(desugared-qq t))]
                           [_ expr])))]

      [('quote _) form]

      [(f* . as*)
       `(,(desugared f*) . ,(if (list? as*) (map desugared as*) (desugared as*)))]

      ;;; gucci.
      [_ form]))

  ;;; because of guard expressions, patterns need to get desugared as well!
  (define (desugared-pattern pattern)
    (match pattern
      [('? (? form? f*)) `(? ,(desugared f*))]
      [('? (? form? f* id)) `(? ,(desugared f*) id)]
      [(h . t) `(,(desugared-pattern h) . ,(desugared-pattern t))]
      [_ pattern]))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  #;[e.g. (desugared '(phi [(x) (* x x)])) ===> (phi [(x) (* x x)])]
  #;[e.g. (desugared '(phi [(x) (* x x)] [(x y) (+ x y)]))
        ===> (phi [(x) (* x x)] [(x y) (+ x y)])]
  #;[e.g. (desugared '`(q w e (not important) ,(let ([(y . ys) x]
                                                   [x (f x)])
                                               (and a b c))))
        ===> `(q w e (not important)
               ,[(phi [((y . ys)) [(phi [(x) (if a (if b c #f) #f)]) (f x)]]) x])]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ;;; ...and finally:
  (value (desugared form) '()))


(define (default-initial-environment) ;; XD
  `([atom? . &atom?]
    [string? . &str?]
    [numeral? . &num?]
    [truth-value? . &tv?]
    [closure? . &closure?]
    [= . &eq?]
    [< . &lt?]
    [+ . &add]
    [* . &mul]
    [- . &sub]
    [/ . &div]
    [% . &mod]
    [++ . &strcat]
    [substr . &substr]
    [strlen . &strlen]))
