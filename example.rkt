#lang eqil

(let t = (< 11 12 13 >) in
  (let r = (|#| 0 t) in
    (halt r)))

(rec (r = (< 1 2 r >)) in
  (halt r))

(rec (r = (< 1 2 r >)) in
  (let x = (|#| 2 r) in
    (halt x)))

(let id = (λ x (halt x)) in
  (switch 3 in
    (3 => (id 1))))

;; The acid test of computer science
(rec (fact = (λ n k
               (let r = (= (n 0))
                 in
                 (switch r in
                   (0 => (k 1))
                   (1 => (let n-1 = (sub1 (n)) in
                           (let m = (λ n-1!
                                      (let t = (* (n n-1!)) in
                                        (k t)))
                             in
                             (fact n-1 m))))))))
  in
  (let id = (λ x (halt x)) in
    (fact 5 id)))
