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
     (PREFIX f l ...))

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
     (more ((ca x) ...) ((ca x) ...) ((ca : ca) := e)) ; A lifting in progress.
     (done (ca : ca) := l))) ; Lifted result


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


(define-metafunction λ-calc-L
  ω : (rc [i] [i]) -> i
  [(ω (rc  [0] [-1])) 1]
  [(ω (rc [-1] [-1])) 2]
  [(ω (rc [-1]  [0])) 3])


(define (sort-trans/racket xs)
  (sort xs (λ (x y) (< (term (ω ,x)) (term (ω ,y)))) #:key first))


(define-metafunction λ-calc-L
  stride : (rc [i] [i]) -> i
  [(stride (rc [i_r] [i_c])) ,(max (abs (term i_r)) (abs (term i_c)))])


; TODO: Implement filling.
(define-metafunction λ-calc-L
  sort&fill : ((ca x) ...) -> ((ca x) ...)
  [(sort&fill ((ca x) ...)) ,(sort-trans/racket (term ((ca x) ...)))])


(define-metafunction λ-calc-L
  row : (rc i i) -> i
  [(row (rc i _)) i])


(define-metafunction λ-calc-L
  column : (rc i i) -> i
  [(column (rc _ i)) i])


(define lift
  (reduction-relation λ-calc-L
    #:domain c
    #:arrow ~>
    ; subst-intrans-∃: An intransitive substitution exists already.
    (~> (more ((ca_1 x_1) ...) ((ca_2 x_2) ... (ca x) (ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L ca)))
        (more ((ca_1 x_1) ...) ((ca_2 x_2) ... (ca x) (ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L x)))
        subst-intrans-∃)

    ; subst-trans-∃: A transitive substitution exists already.
    (~> (more ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ((ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L ca)))
        (more ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ((ca_3 x_4) ...) ((ca_ul : ca_lr) := (in-hole L x)))
        subst-trans-∃)

    ; subst-intrans: The reference is intransitive and there does not already exist a substitution.
    (~> (more ((ca_1 x_1) ...) ((ca_2 x_2) ...)        ((ca_ul : ca_lr) := (in-hole L ca)))
        (more ((ca_1 x_1) ...) ((ca_2 x_2) ... (ca x)) ((ca_ul : ca_lr) := (in-hole L x)))
        (fresh x)
        (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
        (side-condition (not (intersect?/racket (term ((lookup ca ca_r) ...)) (term (ca_r ...)))))
        (side-condition (not (member (term ca) (term (ca_2 ...)))))
        subst-intrans)

    ; subst-trans: The reference is transitive and there does not already exist a substitution.
    (~> (more ((ca_1 x_1) ...)        ((ca_2 x_2) ...) ((ca_ul : ca_lr) := (in-hole L ca)))
        (more ((ca_1 x_1) ... (ca x)) ((ca_2 x_2) ...) ((ca_ul : ca_lr) := (in-hole L x)))
        (fresh x)
        (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
        (side-condition (intersect?/racket (term ((lookup ca ca_r) ...)) (term (ca_r ...))))
        (side-condition (not (member (term ca) (term (ca_1 ...)))))
        subst-trans)

    ; synth-map: The expression has been lifted to a λ-body and there are no transitive references.
    (~> (more ((ca_t x_t) ...) ((ca_i x_i) ...) ((ca_ul : ca_lr) := l))
        (done (ca_ul : ca_lr) := (MAP (λ (x_i ...) l) (extd (ca_ul0 : ca_lr0) (ca_ul : ca_lr)) ...))
        (where (ca_ul0 ...) ((lookup ca_i ca_ul) ...))
        (where (ca_lr0 ...) ((lookup ca_i ca_lr) ...))
        (side-condition (empty? (term (ca_t ...))))
        synth-map)

    ; synth-prefix: The expression has been lifted to a λ-body and there are transitive references.
    (~> (more ((ca_t x_t) ...) ((ca_i x_i) ...) ((ca_ul : ca_lr) := l))
        (done (ca_ul : ca_lr) := (PREFIX (λ (x_t1 x_t2 x_t3 x_i ...) l)
                                        (ca_s : ca_c)
                                        (ca_s : ca_r)
                                        (extd (ca_ul0 : ca_lr0) (ca_ul : ca_lr)) ...))
        (where (ca_ul0 ...) ((lookup ca_i ca_ul) ...))
        (where (ca_lr0 ...) ((lookup ca_i ca_lr) ...))
        (where ((ca_t1 x_t1) (ca_t2 x_t2) (ca_t3 x_t3)) (sort&fill ((ca_t x_t) ...))) ; Make sure this holds!

        ; Construct initial row and column addres
        (where ca_s (lookup ca_t2 ca_ul))
        (where ca_c (rc (row ca_lr) (column ca_s)))
        (where ca_r (rc (row ca_s)  (column ca_lr)))

        (side-condition (not (empty? (term (ca_t ...)))))
        synth-prefix)))


(define s1 (term (more () () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] [2]))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s1 (term (done ((rc 1 1) : (rc 2 2)) := (MAP (λ (x) (x + x)) ((rc 3 3) : (rc 4 4))))))


(define s2 (term (more () () (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] 5))))))
(test-equal (redex-match? λ-calc-L c s2) #t)
(test-->> lift s2 (term (done ((rc 1 1) : (rc 2 2)) := (MAP (λ (x x1) (x + x1))
                                                           ((rc 3 3) : (rc 4 4))
                                                           (HREP ((rc 3 5) : (rc 4 5)) 2)))))

(define s3 (term (more () () (((rc 2 2) : (rc 10 10)) := (((rc [-1] [-1]) + (rc [-1] [0])) + (rc [0] [-1]))))))
(test-equal (redex-match? λ-calc-L c s3) #t)
(test-->> lift s3 (term (done
                        ((rc 2 2) : (rc 10 10))
                        :=
                        (PREFIX
                         (λ (x2 x x1) ((x + x1) + x2))
                         ((rc 1 1) : (rc 10 1))
                         ((rc 1 1) : (rc 1 10))))))

;; (require pict)
;; (send (pict->bitmap (render-reduction-relation lift)) save-file "/tmp/lift-rules.png" 'png 100)
