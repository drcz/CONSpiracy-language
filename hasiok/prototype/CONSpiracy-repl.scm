#! /usr/bin/guile \
--no-auto-compile -s
!# ;; CONSpiracy v 0.1 by drcz, last touch 2016-09-18, Eindhoven ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; the author is extremely grateful to Panicz Godek for nice-9 module,
;; and to euro-garden coffeeshop, for serving excelent coffee :)
(include "CONSpiracy-implementation.scm") ;; "LOAD"
(begin ;; "RUN"
  (display "   (-- ALGORITHMIC LANGUAGE CONSpiracy v0.1 --)") (newline)
  (display "copyleft by Scislav Dercz 2016/09/09-18, Eindhoven") (newline)
  (display "type (halt) to quit") (newline)
  (newline)
  (repl 'READY. *initial-env*))

;; boom! ;)
