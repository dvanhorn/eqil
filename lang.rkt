#lang racket
(require (for-syntax racket/base "make-lang.rkt" "semantics.rkt")
         "semantics.rkt"
         "prims.rkt")
(provide #%top-interaction #%module-begin (all-from-out "prims.rkt"))
(define-syntax #%top-interaction (make-#%top-interaction #'inj #'step expression?))
(define-syntax #%module-begin    (make-#%module-begin    #'inj #'step expression?))