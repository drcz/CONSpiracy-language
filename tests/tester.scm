#! /usr/bin/guile \
--no-auto-compile -s
!#
(use-modules (ice-9 pretty-print))
(include "../conspiracy-semantics.scm")

;;; the idea is it stops or crashes on any failure.
;;; the tests are pretty random and largely incomplete.
;;; TODO: more tests ;)


(define-macro (assert p)
  `(if ,p
       #t
       (begin (display '(assertion ,p failed!))
              (newline)
              (exit))))

(define-macro (assert-eq? p v)
  `(if (equal? ,p ,v)
       #t
       (begin (pretty-print (list 'assert-eq? ',p ,v 'failed!))
              (pretty-print (list 'because ',p '=> ,p))
              (newline)
              (exit))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define EVAL (evaluator (default-initial-environment)))
(define ERROR (lambda (msg) (pretty-print `(ERROR! . ,msg)) (exit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing basic forms))

(assert-eq? (EVAL '() '() ERROR) '())
(assert-eq? (EVAL '42 '() ERROR) '42)
(assert-eq? (EVAL '#t '() ERROR) '#t)
(assert-eq? (EVAL '&atom? '() ERROR) '&atom?)
(assert-eq? (EVAL '"virus from outer space" '() ERROR) '"virus from outer space")

(assert-eq? (EVAL ''qwe '() ERROR) 'qwe)
(assert-eq? (EVAL ''(q w e) '() ERROR) '(q w e))

(assert-eq? (EVAL '(* (+ 2 3) 5) '() ERROR) '25)
(assert-eq? (EVAL '(/ 12 0) '() (lambda (m) m)) '(division by 0 is meaningess))
(assert-eq? (EVAL '(/ 12 3) '() ERROR) '4)
(assert-eq? (EVAL '(- (% 3 5) (% -3 5)) '() ERROR) '1)

(assert-eq? (EVAL '(++ "hi " "there") '() ERROR) '"hi there")
(assert-eq? (EVAL '(substr "qwertyu" 3 5) '() ERROR) '"rt")
(assert-eq? (EVAL '(strlen "qwe") '() ERROR) '3)

(assert-eq? (EVAL '`(2 + 3 = ,(+ 2 3)) '() ERROR) '(2 + 3 = 5))

(assert-eq? (EVAL '(if (= 2 3) 'wat? 'gucci) '() EVAL) 'gucci)

(assert-eq? (EVAL '(or (= 2 3) (= 3 7) (= 6 6)) '() EVAL) '#t)
(assert-eq? (EVAL '(or (= 2 3) (= 3 7) (= 6 9)) '() EVAL) '#f)

(assert-eq? (EVAL '(and (= 2 2) (= 3 3) (= 6 6)) '() EVAL) '#t)
(assert-eq? (EVAL '(and (= 2 2) (= 3 3) (= 6 6) (= 7 9)) '() EVAL) '#f)

(assert-eq? (EVAL '(not (= 2 3)) '() EVAL) '#t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing simple variable bindings))

(assert-eq? (EVAL 'qwe '() (lambda (_) 'wanted-error)) 'wanted-error)
(assert-eq? (EVAL 'qwe '([qwe . 23]) ERROR) '23)
;; ...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing basic phi-forms and lets))

(assert (closure? (EVAL '(phi [(x) x]) '() ERROR)))
(assert-eq? (EVAL '((phi [(x) (* x x)]) (+ 2 3)) '() ERROR) '25)
(assert-eq? (EVAL '(let ([x 23] [y (* x x)]) (/ y 23)) '() ERROR) '23)
(assert-eq? (EVAL '(let ([x '(2 3)] [(a b) x]) (* a b)) '() ERROR) '6)
;; ...

(let ([Y '(phi [(f)
                ((phi [(x) (x x)]) (phi [(g)
                                         (f (phi [as ((g g) . as)]))]))])])

  (assert (closure? (EVAL Y '() ERROR)))
  (assert-eq? (EVAL `[(,Y (phi [(f)
                                (phi [(n) (if (= n 0) 1 (* n (f (- n 1))))])]))
                      0] '() ERROR) '1)
  (assert-eq? (EVAL `[(,Y (phi [(f)
                                (phi [(n) (if (= n 0) 1 (* n (f (- n 1))))])]))
                      5] '() ERROR) '120))

(assert-eq? (EVAL '((phi [(x (? (phi [(y) (not (= x y))]))) 'neq]
                         [_ 'eq]) 2 3) '() ERROR) 'neq)

(assert-eq? (EVAL '((phi [(x (? (phi [(y) (not (= x y))]))) 'neq]
                         [_ 'eq]) 3 3) '() ERROR) 'eq)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing example compendium))

(let* ([test-compendium
        '[ (def sq (phi [x (* x x)]))

           (def square (phi [(x) (* x x)]))

           (def cat (phi [(()       ys) ys]
                         [((x . xs) ys) `(,x . ,(cat xs ys))]))

           (def foldr (phi [(o e ()) e]
                           [(o e (x . xs)) (o x (foldr o e xs))]))

           (def map (phi [(f xs) (foldr (phi [(h t) `(,(f h) . ,t)]) () xs)]))

           (def filter (phi [(p? xs) (foldr (phi [((? p? h) t) `(,h . ,t)]
                                                 [(_ t) t])
                                            ()
                                            xs)]))
           (def sum (phi [(xs) (foldr + 0 xs)]))

           (def sum-of-squares (phi [(xs) (sum (map square xs))]))
           ;; ...
          ]]
       [defs
         (map (lambda (definition)
                (and-let* ([('def id form) definition])
                  `[,id . ,(EVAL form '() ERROR)]))
              test-compendium)])

  (assert (closure? (EVAL 'square defs ERROR)))
  (assert-eq? (EVAL '(square (+ 2 3)) defs ERROR) '25)
  (assert-eq? (EVAL '(sq . 5) defs ERROR) '25)
  (assert-eq? (EVAL '(let [(x (+ 2 3))] (sq . x)) defs ERROR) '25)
  (assert-eq? (EVAL '(cat '(q w e) '(a s d)) defs ERROR) '(q w e a s d))
  (assert-eq? (EVAL '(filter (phi [(x) (not (< x 0))])
                             '(1 0 -3 7 -2 5)) defs ERROR) '(1 0 7 5))
  (assert-eq? (EVAL '(sum-of-squares '(1 2 3 4 5)) defs ERROR) '55)
  ;; ...
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(newline) (pretty-print '(ALL GOOD, DEPLOY!))
(exit)