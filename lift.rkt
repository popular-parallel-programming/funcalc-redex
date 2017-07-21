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
     (HREP l l)
     (VREP l l)
     (SCAN f l ...))

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
     (γ ((ca x) ...) ((ca x) ...) ((ca : ca) := e)) ; A lifting in progress.
     (lft (ca : ca) := l))) ; Lifted result


(define-metafunction λ-calc-L
  extd : e e -> e
  [(extd e_1 e_2) (HREP e_1 (COLUMNS e_2)) (side-condition (eq? 1 (term (COLUMNS e_1))))]
  [(extd e_1 e_2) (VREP e_1 (ROWS e_2))    (side-condition (eq? 1 (term (ROWS e_1))))]
  [(extd e_1 _)   e_1])


(define-metafunction λ-calc-L
  enumerate : ((rc i i) : (rc i i)) -> (ca ...) ; Can only be called with absolute ranges.
  [(enumerate ((rc i_r1 i_c1) : (rc i_r2 i_c2)))
   ,(let [(rows (add1 (- (term i_r2) (term i_r1))))
          (cols (add1 (- (term i_c2) (term i_c1))))]
      (foldl append '()
             (build-list rows
                         (λ (r) (build-list cols
                                            (λ (c) (term (rc ,(add1 r) ,(add1 c)))))))))])


(define (intersect?/racket xs ys)
  (ormap (λ (x) (member x ys)) xs))


(define lift
  (reduction-relation λ-calc-L
    #:domain c
    #:arrow ~>
    ; subst-intrans-∃: An intransitive substitution exists already.
    (~> (γ ((ca_1 x_1) ...) ((ca_2 x_2) ... (ca x) (ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L ca)))
        (γ ((ca_1 x_1) ...) ((ca_2 x_2) ... (ca x) (ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L x)))
        subst-intrans-∃)

    ; subst-trans-∃: A transitive substitution exists already.
    (~> (γ ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ((ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L ca)))
        (γ ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ((ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L x)))
        subst-trans-∃)

    ; subst-intrans: The reference is intransitive and there does not already exist a substitution.
    (~> (γ ((ca_1 x_1) ...) ((ca_2 x_2) ...)        ((ca_ul : ca_lr) := (in-hole L ca)))
        (γ ((ca_1 x_1) ...) ((ca_2 x_2) ... (ca x)) ((ca_ul : ca_lr) := (in-hole L x)))
        (fresh x)
        (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
        (side-condition (not (intersect?/racket (term ((lookup ca ca_r) ...)) (term (ca_r ...)))))
        (side-condition (not (member (term ca) (term (ca_2 ...)))))
        subst-intrans)

    ; subst-trans: The reference is transitive and there does not already exist a substitution.
    ;; (~> (γ ((ca_1 x_1) ...) ((ca_2 x_2) ...) ((ca_ul : ca_lr) := (in-hole L ca)))
    ;;     (γ ((ca_1 x_1) ...) ((ca_2 x_2) ...) ((ca_ul : ca_lr) := (in-hole L x)))
    ;;     (fresh x)
    ;;     (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
    ;;     (side-condition (intersect?/racket (term ((lookup ca ca_r) ...)) (term (ca_r ...))))
    ;;     (side-condition (not (member (term ca) (term (ca_1 ...)))))
    ;;     subst-trans)

    (~> (γ ((ca_1 x_1) ...) ((ca_2 x_2) ...) ((ca_ul : ca_lr) := l))
        (lft (ca_ul : ca_lr) := (MAP (λ (x_2 ...) l) (extd (ca_ul0 : ca_lr0) (ca_ul : ca_lr)) ...))
        (where (ca_ul0 ...) ((lookup ca_2 ca_ul) ...))
        (where (ca_lr0 ...) ((lookup ca_2 ca_lr) ...))
        (side-condition (empty? (term (ca_1 ...))))
        synth-map)))


(define s1 (term (γ () () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] [2]))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s1 (term (lft ((rc 1 1) : (rc 2 2)) := (MAP (λ (x) (x + x)) ((rc 3 3) : (rc 4 4))))))


(define s2 (term (γ () () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] 5))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s2 (term (lft ((rc 1 1) : (rc 2 2)) := (MAP (λ (x x1) (x + x1))
                                                           ((rc 3 3) : (rc 4 4))
                                                           (HREP ((rc 3 5) : (rc 4 5)) 2)))))
