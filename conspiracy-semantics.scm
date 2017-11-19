;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The [operational] semantics of CONSpiracy, aka the Thing.
;;; 2017-11-18, Alicante

(include "conspiracy-syntax.scm") ;; tmp?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; "environments"...

(define binding? ;;; FYI
  (list-of (lambda ((k . v)) (and (identifier? k)
                             (or (closure? v)
                                 (expression? v))))))

(define (lookup binding #;for id)
  (match (assoc id binding)
    [#f '&UNBOUND]
    [(id . expr) expr]))

(define (extended binding #;with id #;as expr)
  `([,id . ,expr] . ,binding)) ;;; TODO: czy delecik?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; internal representation of phi-forms...
(define (closure? x)
  (and-let* ([('&CLOSURE ([(? pattern?) (? form?)] ...) (? binding?)) x])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; the evaluator.

(define (evaluator #;with initial-environment)
  (lambda (#;of form #;in-the-context-of defined #;on-error-applying error)
    (define (value form binding)
      (match form ;;; nb we assert desugared form here.

        [(? constant?) form]
        [(? closure?) form]

        [(? identifier? id) (match (lookup (append binding defined) id)
                              ['&UNBOUND (error `(unbound identifier ,id))]
                              [expr expr])]

        [('phi . cases) `(&CLOSURE ,cases ,binding)] ;;TODO: only FV from binding

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


    (define (matching pattern form #;wrt match-bindings)
      (let matching ([pattern pattern]
                     [form form]
                     [binding '()])
        (match pattern

          ['_ binding]

          [() (and (null? form) binding)]
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

        [('&div (? numeral? n) (? numeral? m)) (quotient n m)]
        [('&div . _) (error `(&div expects 2 numeral arguments))]

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

        [_ (error `(unrecognized primitive application ,app))]))

  ;;; ...and finally:
  (value (desugared form) initial-environment)))


(define (default-initial-environment)
  `([atom? . &atom?]
    [string? . &str?]
    [numeral? . &num?]
    [truth-value? . &tv?]
    [closure? . &closure?]
    [= . &eq?]
    [< . &lt]
    [+ . &add]
    [* . &mul]
    [- . &sub]
    [/ . &div]
    [% . &mod]
    [++ . &strcat]
    [substr . &substr]
    [strlen . &strlen]))
