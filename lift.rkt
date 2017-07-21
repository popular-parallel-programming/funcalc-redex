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
     (MAP f l ...)
     (HUNFOLD l l)
     (VUNFOLD l l))

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
     (γ ((ca x) ...) ((ca : ca) := e)) ; A lifting in progress.
     (lft (ca : ca) := l))) ; Lifted result


(define-metafunction λ-calc-L
  extd : e e -> e
  [(extd e_1 e_2) (HUNFOLD e_1 (COLUMNS e_2)) (side-condition (eq? 1 (term (COLUMNS e_1))))]
  [(extd e_1 e_2) (VUNFOLD e_1 (ROWS e_2))    (side-condition (eq? 1 (term (ROWS e_1))))]
  [(extd e_1 _)   e_1])


(define lift
  (reduction-relation λ-calc-L
    #:domain c
    #:arrow ~>
    (~> (γ ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ((ca_3 : ca_4) := (in-hole L ca)))
        (γ ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ((ca_3 : ca_4) := (in-hole L x)))
        subst-∃)

    (~> (γ ((ca_s x_s) ...)        ((ca_1 : ca_2) := (in-hole L ca)))
        (γ ((ca_s x_s) ... (ca x)) ((ca_1 : ca_2) := (in-hole L x)))
        (fresh x)
        (side-condition (not (member (term ca) (term (ca_s ...)))))
        subst-intrans)

    (~> (γ ((ca x) ...) ((ca_1 : ca_2) := l))
        (lft (ca_1 : ca_2) := (MAP (λ (x ...) l) (extd (ca_ul : ca_lr) (ca_1 : ca_2)) ...)) ; Can be plugged into a σ.
        (where (ca_ul ...) ((lookup ca ca_1) ...))
        (where (ca_lr ...) ((lookup ca ca_2) ...))
        synth)))


(define s1 (term (γ () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] [2]))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s1 (term (lft ((rc 1 1) : (rc 2 2)) := (MAP (λ (x) (x + x)) ((rc 3 3) : (rc 4 4))))))

(define s2 (term (γ () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] 5))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s2 (term (lft ((rc 1 1) : (rc 2 2)) := (MAP (λ (x x1) (x + x1))
                                                           ((rc 3 3) : (rc 4 4))
                                                           (HUNFOLD ((rc 3 5) : (rc 4 5)) 2)))))
