#! /usr/bin/guile \
--no-auto-compile -s
!#

(include "conspiracy-semantics.scm") ;; pff.

(define EVAL (evaluator))

(define (repl output defs thms)
  (let ([ERROR (lambda (msg) (repl `(ERROR: . ,msg) defs thms))])

    (write output) (newline) (display '>)

    (match (catch #t (lambda () (read)) (const #(#;just-to-cause-syntax-error-XD)))

      [('def (? identifier? id) (? form? frm))
       (repl (if (not (eq? (lookup defs id) '&UNBOUND))
                 `(WARNING: redefinition for ,id)
                 `(new definition for ,id))
             (extended defs id (EVAL frm defs ERROR))
             thms)]
      [('def (? identifier?) f) (ERROR `(incorrect form ,f))]
      [('def i _) (ERROR `(,i is not a legal identifier))]

      [('e.g. (? form? frm) '===> (? expression? exp))
       (let ([exp* (EVAL frm defs ERROR)])
         (repl (if (equal? exp exp*)
                   '(yup.)
                   `(WARNING: e.g. form failure, expected
                              ,exp but got ,exp*))
               defs               
               thms))]
      [('e.g. (? form? f) '===> e) (ERROR `(,e is not an expression))]
      [('e.g. f '===> _) (ERROR `(incorrect form ,f))]

      ;;; TODO: maybe e.g. form without "===>" ?

      [('thm. (? form? frm)) (repl `(a theorem, nice to know!)
                                   defs
                                   `(,frm . ,thms))]
      [('thm. f) (ERROR `(incorrect form ,f))]
      
      ['&I-really-want-to-quit-this-CONSpiracy
       (display "Auf Wiedersehen!") (newline) (exit)]

      ['&show-theorems (begin
                           (map (lambda (t)
                                  (pretty-print t #:max-expr-width 150 #:width 150)
                                  (newline))
                                thms)
                           (repl '(------------------------------------------)
                                 defs
                                 thms))]

      [(? form? frm)
       (repl (EVAL frm defs ERROR) defs thms)]
      
      [_ (ERROR '(syntax error))] )))


(define ((fatal-error frm))
  (pretty-print `(FATAL ERROR: initial compendium failed on ,frm))
  (pretty-print '(exiting NOW!))
  (exit))

(define *initial-compendium*
  (append
   (map (lambda (definition)
          (and-let* ([('def (? identifier? id) (? form? form)) definition])
            `[,id . ,(EVAL form '() (fatal-error form))]))
        '[ (def > (phi [(m n) (< n m)])) 
           (def >= (phi [(m n) (not (< m n))]))
           (def <= (phi [(m n) (not (< n m))]))
           #;place-your-initial-defs-here ])
   (default-initial-environment)))

(define *initial-theorems* '()) ;; everything theorem-wise is just a placeholder...


(begin ;; "RUN"
  (display "  **** the PSYCHODELIC LANGUAGE CONSpiracy v0.33 ****") (newline)
  (display "  Scislav Dercz 2016-17 @ Eindhoven, Gdynia, Alicante") (newline)
  (newline)
  (display "type &I-really-want-to-quit-this-CONSpiracy to quit") (newline)
  (newline)
  (repl 'READY. *initial-compendium* *initial-theorems*))
