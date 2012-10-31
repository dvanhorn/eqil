#lang racket
(require redex/reduction-semantics)
(require "lang.rkt")

(test-->> step 
          (term ((let x = 3 in (halt x)) () ()))
          (term ((halt x) 
                 ((x 0))
                 ((0 3)))))

(test-->> step
          (term ((let x = 6 in
                   (let y = 3 in
                     (let z = (+ (x y)) in
                       (halt z))))
                 ()
                 ()))
          (term ((halt z)
                 ((z 2)
                  (y 1)
                  (x 0))
                 ((2 9)
                  (1 3)
                  (0 6)))))

(test-->> step
          (term ((let x = 6 in
                   (let y = 3 in
                     (let z = (< x y >) in
                       (halt z))))
                 ()
                 ()))
          (term ((halt z)
                 ((z 2)
                  (y 1)
                  (x 0))
                 ((2 ((< x y >) ((y 1) (x 0))))
                  (1 3)
                  (0 6)))))

(test-->> step
          (term ((let w = 6 in
                   (let x = 3 in
                     (let y = (< w x >) in
                       (let z = (|#| 0 y) in
                         (halt z)))))
                 ()
                 ()))
          (term ((halt z)
                 ((z 3)
                  (y 2)
                  (x 1)
                  (w 0))
                 ((3 6)
                  (2 ((< w x >) ((x 1) (w 0))))
                  (1 3)
                  (0 6)))))

(test-->> step
          (term ((let w = 6 in
                   (let x = 3 in
                     (let y = (< w x >) in
                       (let z = (|#| 1 y) in
                         (halt z)))))
                 ()
                 ()))
          (term ((halt z)
                 ((z 3)
                  (y 2)
                  (x 1)
                  (w 0))
                 ((3 3)
                  (2 ((< w x >) ((x 1) (w 0))))
                  (1 3)
                  (0 6)))))

(test-->> step
          (term ((let x = (λ y (halt y)) in
                   (halt x))
                 ()
                 ()))
          (term ((halt x)
                 ((x 0))
                 ((0 ((λ y (halt y)) ()))))))

(test-->> step
          (term ((let x = (λ y (halt y)) in
                   (let z = 3 in
                     (x z)))
                 ()
                 ()))
          (term ((halt y)
                 ((y 2))
                 ((2 3)
                  (1 3)
                  (0 ((λ y (halt y)) ()))))))

(test-->> step
          (term ((let x = 3 in
                   (switch x in
                           (1 => (let y = 0 in (halt y)))
                           (3 => (halt x))
                           (5 => (let z = 0 in (halt y)))))
                 ()
                 ()))
          (term ((halt x)
                 ((x 0))
                 ((0 3)))))

(require redex)
(traces step
        (term ((rec 
                 (f = (λ y (g y)))
                 (g = (λ z (halt z)))
                 in
                 (g f))
               ()
               ())))

#;
(redex-match EQIL
             ((X F) ... ρ σ)
             (term ((f (λ y (g y)))
                    (g (λ z (halt z)))
                    ()
                    ())))