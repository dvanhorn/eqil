#lang racket
(require redex/reduction-semantics
         (only-in "semantics.rkt" QIL inj))

(provide AQIL inj astep expression?)

;; Abstract runtime language for Coq IL
(define-extended-language AQIL QIL
  ;; Just like EQIL but stores map locations to *sets* of storables.
  (Σ ::= (E ρ σ))
  (ρ ::= ((X A) ...))
  (σ ::= ((A SS) ...))
  (A ::= any)
  (S ::= ;; Storables
     ((< V ... >) ρ)
     ((λ X ... E) ρ)
     num
     C)
  (SS ::= {S ...}))

(define (expression? x)
  (redex-match AQIL E x))

;; Reduction relation for Abstract Coq IL
(define astep
  (reduction-relation 
   AQIL #:domain Σ
   (--> ((X V_0 ..._1) ρ σ)
        (E ρ_1 σ_1)
        ;; Non-deterministically choose a function to apply
        (where (S_0 ... ((λ X_1 ..._1 E) ρ_0) S_1 ...) (deref^ X ρ σ))
        (where (SS ...) ((deref^ V_0 ρ σ) ...))
        (where (ρ_1 σ_1) (bind^ (X_1 SS) ... ρ_0 σ))
        app)
   (--> ((let X = D in E) ρ σ)
        (E ρ_0 σ_0)
        (where (ρ_0 σ_0) (push^ X D ρ σ))
        let)
   (--> ((rec (X = F) ... in E) ρ σ)
        (E ρ_0 σ_0)
        (where (ρ_0 σ_0) (recbind^ (X F) ... ρ σ))
        rec)
   (--> ((switch V in 
                 (C_0 => E_0)
                 ...
                 (C => E)
                 (C_1 => E_1)
                 ...)
         ρ σ)
        (E ρ σ)
        ;; Non-determinstically choose const to switch on
        (where (S_0 ... C S_1 ...) (deref^ V ρ σ))
        switch)
   (--> ((switch V in 
                 (C_0 => E_0)
                 ...
                 (C => E)
                 (C_1 => E_1)
                 ...)
         ρ σ)
        (E ρ σ)
        ;; Non-determinstically choose const to switch on
        (where (S_0 ... num S_1 ...) (deref^ V ρ σ))
        switch-abs)))

(define-metafunction AQIL
  deref^ : V ρ σ -> SS
  [(deref^ C ρ σ) {C}]
  [(deref^ X 
          ((X_0 A_0) ... (X A) (X_1 A_1) ...)
          ((A_2 SS_0) ... (A SS) (A_3 SS_1) ...))
   SS])

(define-metafunction AQIL
  bind^ : (X SS) ... ρ σ -> (ρ σ)
  [(bind^ ρ σ) (ρ σ)]
  [(bind^ (X SS) (X_1 SS_1) ... ρ σ)
   (bind^ (X_1 SS_1) ...
          (extend-env ρ X A)
          (join-sto σ A SS))
   (where A (alloc^ σ X))])

(define-metafunction AQIL
  alloc^ : σ X -> A
  [(alloc^ σ X) X])

(define-metafunction AQIL
  push^ : X D ρ σ -> (ρ σ)
  [(push^ X D ρ σ)
   ((extend-env ρ X A)
    (join-sto σ A SS))
   (where SS (reduce^ D ρ σ))
   (where A (alloc^ σ X))])

(define-metafunction AQIL
  reduce^ : D ρ σ -> SS
  [(reduce^ C ρ σ) {C}]
  [(reduce^ (PRIM V ...) ρ σ)
   {(∆^ PRIM C ...)}
   (where ((S_0 ... C S_1 ...) ...) ((deref^ V ρ σ) ...))]   
  [(reduce^ (I V) ρ σ)
   (deref^ V_0 ρ_0 σ)
   ;; Non-deterministically choose tuple to dereference
   (where (S_0 ... ((< V_i ... >) ρ_i) S_1 ...) (deref^ V ρ σ))
   (where (V_0 ρ_0) (ith ((< V_i ... >) ρ_i) I))]
  [(reduce^ (< V ... >) ρ σ)
   {((< V ... >) ρ)}]
  [(reduce^ (λ X ... E) ρ σ)
   {((λ X ... E) ρ)}])

(define-metafunction AQIL
  ∆^ : PRIM C ... -> C or num
  [(∆^ PRIM C ...) num])

(define-metafunction AQIL
  recbind^ : (X F) ... ρ σ -> (ρ σ)
  [(recbind^ (X F) ... ρ σ)
   (ρ_0 σ_0)
   (where (A ...) (alloc^* σ X ...))
   (where ρ_0 (extend-env* ρ (X A) ...))
   (where (S ...) ((F ρ_0) ...))
   (where σ_0 (join-sto* σ (A {S}) ...))])

(define-metafunction AQIL
  alloc^* : σ X ... -> (A ...)
  [(alloc^* σ X ...) (X ...)])

(define-metafunction AQIL
  extend-env* : ρ (X A) ... -> ρ
  [(extend-env* ρ) ρ]
  [(extend-env* ρ (X A) (X_1 A_1) ...)
   (extend-env* (extend-env ρ X A)
                (X_1 A_1) ...)])

(define-metafunction AQIL
  join-sto* : σ (A SS) ... -> σ
  [(join-sto* σ) σ]
  [(join-sto* σ (A SS) (A_1 SS_1) ...)
   (join-sto* (join-sto σ A SS)
              (X_1 A_1) ...)])
   

(define-metafunction AQIL
  ith : ((< V ... >) ρ) I -> (V ρ)
  [(ith ((< V ... >) ρ) I)
   (,(list-ref (term (V ...)) (term I)) ρ)])

;; ρ[X ↦ A]
(define-metafunction AQIL
  extend-env : ρ X A -> ρ
  [(extend-env ((X_0 A_0) ... (X A_n) (X_1 A_1) ...) X A)
   ((X_0 A_0) ... (X A) (X_1 A_1) ...)]
  [(extend-env ((X_0 A_0) ...) X A)
   ((X A) (X_0 A_0) ...)])

;; σ ⊔ [A ↦ {S ..}]
(define-metafunction AQIL
  join-sto : σ A SS -> σ
  [(join-sto ((A_0 SS_0) ... (A SS_n) (A_1 SS_1) ...) A SS)
   ((A_0 SS_0) ... (A (union SS_n SS)) (A_1 SS_1) ...)]
  [(join-sto ((A_0 SS_0) ...) A SS)
   ((A SS) (A_0 SS_0) ...)])

;; Sets are represented as sorted lists of unique elements.
(define-metafunction AQIL
  union : (any ...) (any ...) -> (any ...)
  [(union any_0 any_1)
   ,(let ((s (set-union (apply set (term any_0))
                        (apply set (term any_1)))))
      (sort (set->list s) sexp<))])

(define (sexp< s1 s2)
  (cond [(and (atom? s1) (cons? s2)) true]
        [(and (atom? s1) (atom? s2))
         (atom< s1 s2)]
        [(and (cons? s1) (atom? s2)) false]
        [(and (cons? s1) (cons? s2))
         (and (sexp< (car s1) (car s2))
              (sexp< (cdr s1) (cdr s2)))]))

(define (atom? x) (or (number? x) (symbol? x)))

(define (atom< a1 a2)
  (cond [(and (symbol? a1) (number? a2)) true]
        [(and (symbol? a1) (symbol? a2))
         (string<? (symbol->string a1)
                  (symbol->string a2))]
        [(and (number? a1) (symbol? a2)) false]
        [(and (number? a1) (number? a2)) (< a1 a2)]))



  

