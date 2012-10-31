#lang racket
(require redex/reduction-semantics)
(provide step inj recbind EQIL expression?)

;; Semantics for Coq IL using store allocated constants

;; Static language for Coq IL
(define-language QIL
  ;; Values
  (V ::= X C)
  
  ;; Expressions
  (E ::= 
     (V V ...)
     (let X = D in E)
     (rec (X = F) ... in E)
     (switch V in (C => E) ...)
     (halt V))
  
  (D ::=
     (PRIM (V ...))      ;; Primitive application
     (< V ... >)         ;; Tuple
     (|#| I V)           ;; Tuple projection
     (λ X ... E))        ;; Function
  
  (F ::= ;; Subset of D safe for recursive binding
     ;; Recursive functions are represented by
     ;; recursive tuples after closure conerversion.
     (< V ... >)
     (λ X ... E))
  
  ;; Primitives
  (PRIM ::= add1 sub1 + - * / =)
  
  ;; Constants
  (C ::= number)
  
  ;; Indexes
  (I ::= natural)
  
  ;; Variables
  (X ::= variable-not-otherwise-mentioned))

(define (expression? x)
  (redex-match EQIL E x))

;; Runtime language for Coq IL
(define-extended-language EQIL QIL
  ;; At runtime, environments map variables to locations
  ;; and the heap maps locations to storable values, i.e.
  ;; tuples, functions, and constants.
  (Σ ::= (E ρ σ))
  (ρ ::= ((X A) ...))
  (σ ::= ((A S) ...))
  (A ::= natural)
  (S ::= ;; Storables
     ((< V ... >) ρ)
     ((λ X ... E) ρ)
     C))

;; Reduction relation for Coq IL
(define step
  (reduction-relation 
   EQIL #:domain Σ
   (--> ((X V_0 ..._1) ρ σ)
        (E ρ_1 σ_1)
        (where ((λ X_1 ..._1 E) ρ_0) (deref X ρ σ))
        (where (S ...) ((deref V_0 ρ σ) ...))
        (where (ρ_1 σ_1) (bind (X_1 S) ... ρ_0 σ))
        app)
   (--> ((let X = D in E) ρ σ)
        (E ρ_0 σ_0)
        (where (ρ_0 σ_0) (push X D ρ σ))
        let)
   (--> ((rec (X = F) ... in E) ρ σ)
        (E ρ_0 σ_0)
        (where (ρ_0 σ_0) (recbind (X F) ... ρ σ))
        rec)
   (--> ((switch V in 
                 (C_0 => E_0)
                 ...
                 (C => E)
                 (C_1 => E_1)
                 ...)
         ρ σ)
        (E ρ σ)
        (where C (deref V ρ σ))
        switch)))

(define-metafunction EQIL
  inj : E -> Σ
  [(inj E) (E () ())])

(define-metafunction EQIL
  bind : (X S) ... ρ σ -> (ρ σ)
  [(bind ρ σ) (ρ σ)]
  [(bind (X S) (X_1 S_1) ... ρ σ)
   (bind (X_1 S_1) ... 
         (extend-env ρ X A)
         (extend-sto σ A S))
   (where A (alloc σ X))])
 
(define-metafunction EQIL
  recbind : (X F) ... ρ σ -> (ρ σ)
  [(recbind (X F) ... ρ σ)
   (ρ_0 σ_0)
   (where (A ...) (alloc* σ X ...))
   (where ρ_0 (extend-env* ρ (X A) ...))
   (where (S ...) ((F ρ_0) ...))
   (where σ_0 (extend-sto* σ (A S) ...))])

(define-metafunction EQIL
  push : X D ρ σ -> (ρ σ)
  [(push X D ρ σ)
   ((extend-env ρ X A)
    (extend-sto σ A S))
   (where S (reduce D ρ σ))
   (where A (alloc σ X))])

(define-metafunction EQIL
  extend-env* : ρ (X A) ... -> ρ
  [(extend-env* ρ) ρ]
  [(extend-env* ρ (X A) (X_1 A_1) ...)
   (extend-env* (extend-env ρ X A)
                (X_1 A_1) ...)])

;; ρ[X ↦ A]
(define-metafunction EQIL
  extend-env : ρ X A -> ρ
  [(extend-env ((X_0 A_0) ... (X A_n) (X_1 A_1) ...) X A)
   ((X_0 A_0) ... (X A) (X_1 A_1) ...)]
  [(extend-env ((X_0 A_0) ...) X A)
   ((X A) (X_0 A_0) ...)])

(define-metafunction EQIL
  extend-sto* : σ (A S) ... -> σ
  [(extend-sto* σ) σ]
  [(extend-sto* σ (A S) (A_1 S_1) ...)
   (extend-sto* (extend-sto σ A S)
                (X_1 A_1) ...)])

;; σ[A ↦ S]
(define-metafunction EQIL
  extend-sto : σ A S -> σ
  [(extend-sto ((A_0 S_0) ... (A S_n) (A_1 S_1) ...) A S)
   ((A_0 S_0) ... (A S) (A_1 S_1) ...)]
  [(extend-sto ((A_0 S_0) ...) A S)
   ((A S) (A_0 S_0) ...)])

(define-metafunction EQIL
  alloc* : σ X ... -> (A ...)
  [(alloc* σ X ...)
   ,(let ((a (term (alloc σ x))))
      (for/list ([i (length (term (X ...)))])
        (+ a i)))])
   
  
(define-metafunction EQIL
  alloc : σ X -> A
  [(alloc () X) 0]
  [(alloc ((A S) ...) X)
   ,(add1 (apply max (term (A ...))))])

(define-metafunction EQIL
  ith : ((< V ... >) ρ) I -> (V ρ)
  [(ith ((< V ... >) ρ) I)
   (,(list-ref (term (V ...)) (term I)) ρ)])

(define-metafunction EQIL
  reduce : D ρ σ -> S
  [(reduce C ρ σ) C]
  [(reduce (PRIM (V ...)) ρ σ)
   (∆ PRIM (deref V ρ σ) ...)]   
  [(reduce (|#| I V) ρ σ)
   (deref V_0 ρ_0 σ)
   (where (V_0 ρ_0) (ith (deref V ρ σ) I))]
  [(reduce (< V ... >) ρ σ)
   ((< V ... >) ρ)]
  [(reduce (λ X ... E) ρ σ)
   ((λ X ... E) ρ)])

(define-metafunction EQIL
  deref : V ρ σ -> S
  [(deref C ρ σ) C]
  [(deref X 
          ((X_0 A_0) ... (X A) (X_1 A_1) ...)
          ((A_2 S_0) ... (A S) (A_3 S_1) ...))
   S])
  
(define-metafunction EQIL
  ∆ : PRIM C ... -> C
  [(∆ add1 number)
   ,(add1 (term number))]
  [(∆ sub1 number)
   ,(sub1 (term number))]
  [(∆ + number_1 number_2)
   ,(+ (term number_1) (term number_2))]
  [(∆ = number_1 number_2)
   ,(if (= (term number_1) (term number_2))
        0
        1)]
  [(∆ * number_1 number_2)
   ,(* (term number_1) (term number_2))]
  [(∆ / number_1 number_2)
   ,(/ (term number_1) (term number_2))])
