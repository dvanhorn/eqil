#lang racket
(require (for-syntax racket/base "make-lang.rkt" "abstract-semantics.rkt")
         "abstract-semantics.rkt"
         "prims.rkt")
(provide #%top-interaction #%module-begin (all-from-out "prims.rkt"))
(define-syntax #%top-interaction (make-#%top-interaction #'inj #'astep expression?))
(define-syntax #%module-begin    (make-#%module-begin    #'inj #'astep expression?))