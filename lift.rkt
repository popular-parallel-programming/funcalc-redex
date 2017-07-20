#lang racket

(require redex
         "mini-calc.rkt"
         "lambda-calc.rkt")


(define-extended-language λ-calc-L λ-calc
  (l ::=
     v
     x
     (l + l)
     (l = l)
     (IF l l l)
     (ca : ca)
     (MAP f l ...))

  (L ::=
     hole
     (L + e)
     (l + L)
     (L = e)
     (l = L)
     (IF L e e)
     (IF l L e)
     (IF l l L))

  (c ::=
     (γ (ca ...) (x ...) ((ca : ca) := e))
     (lft (ca : ca) := l))

  (Γ :: =
     (γ (ca ...) (x ...) ((ca : ca) := L))))


(define lift
  (reduction-relation λ-calc-L
    #:domain c
    (--> (γ (ca_1 ..._1 ca ca_2 ...) (x_1 ..._1 x x_2 ...) ((ca_3 : ca_4) := (in-hole L ca)))
         (γ (ca_1 ...   ca ca_2 ...) (x_1 ...   x x_2 ...) ((ca_3 : ca_4) := (in-hole L x)))
         subst-∃)

    (--> (γ (ca_s ...)    (x_s ...)   ((ca_1 : ca_2) := (in-hole L ca)))
         (γ (ca_s ... ca) (x_s ... x) ((ca_1 : ca_2) := (in-hole L x)))
         (fresh x)
         (side-condition (not (member (term ca) (term (ca_s ...)))))
         subst-fresh)

    (--> (γ (ca ...) (x ...) ((ca_1 : ca_2) := l))
         (lft (ca_1 : ca_2) := (MAP (λ (x ...) l) (ca_ul : ca_lr) ...)) ; Can be plugged into a σ.
         (where (ca_ul ...) ,(map (λ (x) (term (lookup ,x ca_1))) (term (ca ...))))
         (where (ca_lr ...) ,(map (λ (x) (term (lookup ,x ca_2))) (term (ca ...))))
         synth)))


(define s1 (term (γ () () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] [2]))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s1 (term (lft ((rc 1 1) : (rc 2 2)) := (MAP (λ (x) (x + x)) ((rc 3 3) : (rc 4 4))))))

(define s2 (term (γ () () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] 5))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s2 (term (lft ((rc 1 1) : (rc 2 2)) := (MAP (λ (x x1) (x + x1))
                                                           ((rc 3 3) : (rc 4 4))
                                                           ((rc 3 5) : (rc 4 5))))))
(traces lift s2)
