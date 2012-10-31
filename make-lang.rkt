#lang racket
(provide make-#%top-interaction make-#%module-begin)
(require syntax/parse
         redex/reduction-semantics
         "semantics.rkt"
         (for-template racket redex "lexical.rkt"))

(define-syntax-class trace-opt
  [pattern (~datum stepper) #:attr sym 'stepper]
  [pattern (~datum traces)  #:attr sym 'traces])

(define ((make-#%top-interaction inj R typable?) stx)
  (syntax-parse stx
    [(_ . e)
     (unless (typable? (syntax->datum #'e))
       (raise-syntax-error 'type-error "ill-formed expression" #'e))
     #`(apply values (apply-reduction-relation* #,R (term (#,inj e))))]))

(define ((make-#%module-begin inj R typable?) stx)
  (syntax-parse stx
    [(_ (~optional trace:trace-opt #:defaults ([trace.sym #f]))
        e ...)
     (for-each (λ (e)
                 (unless (typable? (syntax->datum e))
                   (raise-syntax-error 'type-error "ill-formed expression" e)))
               (syntax->list #'(e ...)))
     (define trace (attribute trace.sym))
     #`(#%module-begin
        (lexical e) ...
        #,(if trace
              #'(reduction-steps-cutoff 100)
              #'(void))
        (initial-char-width 140)        
        #,(case trace
            [(traces) 
             #`(begin (traces #,R (term (#,inj e))) ...)]
            [(stepper)
             #`(begin (stepper #,R (term (#,inj e))) ...)]
            [else
             #'(void)])
              
        (apply values (append (apply-reduction-relation* #,R (term (#,inj e))) ...)))]))