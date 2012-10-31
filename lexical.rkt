#lang racket
(provide lexical)
(require (only-in "prims.rkt" rec switch let))

(define-syntax (lexical stx)
  (syntax-case stx ()
    [(_ e) #'(void (λ () (lx e)))]))

(require (for-syntax syntax/stx))
(define-syntax (lx stx)
  (syntax-case stx (λ • : err let = in rec => |#|)
    [(_ (let x = e in e0))
     (nice stx #'(let ((x (lx e))) (lx e0)))] 
    [(_ (switch v in (c => e) ...))
     (nice stx #'(case v
                   ((c) (lx e)) ...))]
    [(_ (λ x ... e))
     (nice stx #'(λ (x ...) (lx e)))]
    [(_ (rec (x = e) ... in e0))
     (nice stx #'(letrec ((x (lx e)) ...) (lx e0)))]
    [(_ (|#| i v))
     #'(list i (lx v))]
    
    #;
    [(_ (if0 e0 e1 e2))
     (nice stx #'(if (lx e0)
                     (lx e1)
                     (lx e2)))]
    
    [(_ (err _ string)) #'string]
    [(_ ()) #''()]
       
    [(_ (e ...))
     #'((lx e) ...)]
    [(_ e) #'e]))

(define-for-syntax (nice ctx stx)
  (syntax-track-origin  
   stx
   (stx-car (stx-cdr ctx))
   (syntax-local-introduce (stx-car (stx-car (stx-cdr ctx))))))
