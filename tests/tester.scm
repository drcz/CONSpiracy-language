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

(define DEFS (default-initial-environment))
(define EVAL (evaluator))
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

(assert-eq? (EVAL '(* (+ 2 3) 5) DEFS ERROR) '25)
(assert-eq? (EVAL '(/ 12 0) DEFS (lambda (m) m)) '(division by 0 is meaningless))
(assert-eq? (EVAL '(/ 12 3) DEFS ERROR) '4)
(assert-eq? (EVAL '(/ 11 3) DEFS ERROR) '3)
(assert-eq? (EVAL '(- (% 3 5) (% -3 5)) DEFS ERROR) '1)

(assert-eq? (EVAL '(++ "hi " "there") DEFS ERROR) '"hi there")
(assert-eq? (EVAL '(strlen "qwe") DEFS ERROR) '3)
(assert-eq? (EVAL '(substr "qwertyu" 3 5) DEFS ERROR) '"rt")
(assert-eq? (EVAL '(substr "qwertyu" 3 100) DEFS ERROR) '"rtyu")
(assert-eq? (EVAL '(substr "qwertyu" 3) DEFS ERROR) '"rtyu")
(assert-eq? (EVAL '(substr "qwertyu" 100) DEFS ERROR) '"")
(assert-eq? (EVAL '(substr "qwertyu" 100 101) DEFS ERROR) '"")
(assert-eq? (EVAL '(substr "qwertyu" -1) DEFS ERROR) '"")
(assert-eq? (EVAL '(substr "qwertyu" 3 2) DEFS ERROR) '"")

(assert-eq? (EVAL '`(2 + 3 = ,(+ 2 3)) DEFS ERROR) '(2 + 3 = 5))

(assert-eq? (EVAL '(if (= 0 1) 'wat? 'gucci) DEFS ERROR) 'gucci)

(assert-eq? (EVAL '(or (= 2 3) (= 3 7) (= 6 6)) DEFS ERROR) '#t)
(assert-eq? (EVAL '(or (= 2 3) (= 3 7) (= 6 9)) DEFS ERROR) '#f)

(assert-eq? (EVAL '(and (= 2 2) (= 3 3) (= 6 6)) DEFS ERROR) '#t)
(assert-eq? (EVAL '(and (= 2 2) (= 3 3) (= 6 6) (= 7 9)) DEFS ERROR) '#f)

(assert-eq? (EVAL '(not (= 2 3)) DEFS ERROR) '#t)

(assert-eq? (EVAL '(num<-str "13") DEFS ERROR) '13)
(assert-eq? (EVAL '(num<-str "wat?") DEFS ERROR) '0)
(assert-eq? (EVAL '(str<-num 12) DEFS ERROR) '"12")
(assert-eq? (EVAL '(str<-num "q") DEFS (lambda (m) m))
            '(&num2str expects 1 numeral argument))

(assert-eq? (EVAL '(numeral? 23) DEFS ERROR) '#t)
(assert-eq? (EVAL '(numeral? 'qwe) DEFS ERROR) '#f)
(assert-eq? (EVAL '(symbol? 'qwe) DEFS ERROR) '#t)
(assert-eq? (EVAL '(string? "qwe") DEFS ERROR) '#t)
(assert-eq? (EVAL '(closure? (phi [(x) x])) DEFS ERROR) '#t)
(assert-eq? (EVAL '(truth-value? #t) DEFS ERROR) '#t)
(assert-eq? (EVAL '(truth-value? '#t) DEFS ERROR) '#t)
(assert-eq? (EVAL '(truth-value? (= 0 1)) DEFS ERROR) '#t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing simple variable bindings))

(assert-eq? (EVAL 'qwe '() (lambda (msg) msg)) '(unbound identifier qwe))
(assert-eq? (EVAL 'qwe '([qwe . 23]) ERROR) '23)
;; ...

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing basic phi-forms, lets and matches))

(assert (closure? (EVAL '(phi [(x) x]) '() ERROR)))
(assert-eq? (EVAL '((phi [(x) (* x x)]) (+ 2 3)) DEFS ERROR) '25)
(assert-eq? (EVAL '(let ([x 23] [y (* x x)]) (/ y 23)) DEFS ERROR) '23)
(assert-eq? (EVAL '(let ([x '(2 3)] [(a b) x]) (* a b)) DEFS ERROR) '6)
;; ...

(let ([Y '(phi [(f)
                ((phi [(x) (x x)]) (phi [(g)
                                         (f (phi [as ((g g) . as)]))]))])])

  (assert (closure? (EVAL Y '() ERROR)))
  (assert-eq? (EVAL `[(,Y (phi [(f)
                                (phi [(n) (if (= n 0) 1 (* n (f (- n 1))))])]))
                      0] DEFS ERROR) '1)
  (assert-eq? (EVAL `[(,Y (phi [(f)
                                (phi [(n) (if (= n 0) 1 (* n (f (- n 1))))])]))
                      5] DEFS ERROR) '120))

(assert-eq? (EVAL '((phi [(x (? (phi [(y) (not (= x y))]))) 'neq]
                         [_ 'eq]) 2 3) DEFS ERROR) 'neq)

(assert-eq? (EVAL '((phi [(x (? (phi [(y) (not (= x y))]))) 'neq]
                         [_ 'eq]) 3 3) DEFS ERROR) 'eq)

(assert-eq? (EVAL '(match `(hey ,(+ 2 3))
                     [('ho _) 'boo]
                     [('hi _) 'boo]
                     [('hey n) n])
                  DEFS ERROR) '5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(pretty-print '(testing tricky expressions))

(assert-eq? (EVAL '`(qwe ,((phi [(x) (* x x)]) (+ 2 3))) DEFS ERROR) '(qwe 25))

(assert-eq? (EVAL '[(phi [(x) `(qwe ,((phi [(y) (* y x)]) (+ 2 3)))]) (- 9 6)]
                  DEFS ERROR) '(qwe 15))

(assert-eq? (EVAL '(let ([(a p?) `(3 ,(phi [(x) (< 0 x)]))])
                     [(phi [(x) `(qwe ,((phi [(? p? x) (* x x)] [_ 23]) . a))])
                      (- 9 6)])
                  DEFS ERROR) '(qwe 9))

(assert-eq? (EVAL '(let ([(a p?) `(,(- 1 3) ,(phi [(x) (< 0 x)]))])
                     [(phi [(x) `(qwe ,((phi [(? p? x) (* x x)] [_ 23]) . a))])
                      (- 9 6)])
                  DEFS ERROR) '(qwe 23))


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
       [defs (append DEFS
                     (map (lambda (definition)
                            (and-let* ([('def id form) definition])
                              `[,id . ,(EVAL form '() ERROR)]))
                          test-compendium))])

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
