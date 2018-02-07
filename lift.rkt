#lang racket

(require redex
         "mini-calc.rkt"
         "lambda-calc.rkt")


(define-extended-language λ-calc-L λ-calc
  (l ::=
     v
     x                      ; Variable names replace relative cell references.
     (l + l)
     (l = l)
     (IF l l l)
     (rc i i)               ; Only absolute cell references.
     ((rc i i) : (rc i i))  ; Only absolute cell ranges.
     (MAP f l ...)
     (HREP l l)
     (VREP l l)
     (PREFIX f l ...)
     (SUM l ...)
     (SLICE l l l l l))     ; SLICE(arr, r1, c1, r2, c2)

  (L ::=
     hole
     (L + e)
     (l + L)
     (L = e)
     (l = L)
     (IF L e e)
     (IF l L e)
     (IF l l L)
     (SUM l ... L e ...))

  (c ::=
     ; A lifting in progress.
     (more ((ca x) ...)        ; Transitive substitutions
           ((ca x) ...)        ; Intransitive substitutions
           (x x)
           ((ca : ca) := e))

     ; Lifted result
     (done (ca : ca) := l)))


(define-metafunction λ-calc-L
  extd : e e -> e
  [(extd e_1 e_2) (HREP e_1 (COLUMNS e_2)) (side-condition (eq? 1 (term (COLUMNS e_1))))]
  [(extd e_1 e_2) (VREP e_1 (ROWS e_2))    (side-condition (eq? 1 (term (ROWS e_1))))]
  [(extd e_1 _)   e_1])


(define (intersect?/racket xs ys)
  (ormap (λ (x) (member x ys)) xs))


(define-metafunction λ-calc-L
  ω : (rc [i] [i]) -> i
  [(ω (rc [0] [_])) 1]
  [(ω (rc [_] [0])) 3]
  [(ω (rc [_] [_])) 2])


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
    (~> (more ((ca_1 x_1) ...)                       ; Transitive
              ((ca_2 x_2) ... (ca x) (ca_3 x_4) ...) ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L ca)))

        (more ((ca_1 x_1) ...)                       ; Transitive
              ((ca_2 x_2) ... (ca x) (ca_3 x_4) ...) ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L x)))
        exist-i)

    ; subst-trans-∃: A transitive substitution exists already.
    (~> (more ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ; Transitive
              ((ca_3 x_4) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L ca)))

        (more ((ca_1 x_1) ... (ca x) (ca_2 x_2) ...) ; Transitive
              ((ca_3 x_4) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L x)))
        exist-t)

    ; subst-intrans: The reference is intransitive and there does not
    ; already exist a substitution.
    (~> (more ((ca_1 x_1) ...)                       ; Transitive
              ((ca_2 x_2) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L ca)))   ; Lifting

        (more ((ca_1 x_1) ...)                       ; Transitive
              ((ca_2 x_2) ... (ca x))                ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L x)))

        (fresh x)
        (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
        (side-condition (not (intersect?/racket (term ((lookup ca ca_r) ...)) (term (ca_r ...)))))
        (side-condition (not (member (term ca) (term (ca_2 ...)))))
        subst-i)

    ; subst-trans: The reference is transitive and there does not
    ; already exist a substitution.
    (~> (more ((ca_1 x_1) ...)                       ; Transitive
              ((ca_2 x_2) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L ca)))

        (more ((ca_1 x_1) ... (ca x))                ; Transitive
              ((ca_2 x_2) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L x)))

        (fresh x)
        (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
        (side-condition (intersect?/racket (term ((lookup ca ca_r) ...)) (term (ca_r ...))))
        (side-condition (not (member (term ca) (term (ca_1 ...)))))
        (side-condition (= 1 (term (stride ca))))
        subst-t)

    ; subst-area: Substitute an area by a call to SLICE.
    (~> (more ((ca_t x_t) ...)                       ; Transitive
              ((ca_i x_i) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L (ca_1 : ca_2))))

        (more ((ca_t x_t) ...)                       ; Transitive
              ((ca_i x_i) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := (in-hole L (SLICE (ca_ul1 : ca_lr2)
                                                    x_r
                                                    x_c
                                                    (ROWS    ((lookup ca_1 ca_ul) : (lookup ca_2 ca_ul)))
                                                    (COLUMNS ((lookup ca_1 ca_ul) : (lookup ca_2 ca_ul)))))))

        ;; (where (ca_a ...) (enumerate ((lookup ca_1 ca_ul) : (lookup ca_2 ca_lr))))
        ;; (where (ca_r ...) (enumerate (ca_ul : ca_lr)))
        ;; (side-condition (not (intersect?/racket (term (ca_a ...)) (term (ca_r ...)))))

        (where ca_ul1 (lookup ca_1 ca_ul)) ; Upper-left of area.
        (where ca_lr2 (lookup ca_2 ca_lr)) ; Lower-right of area.
        subst-area)


    ; synth-map: The expression has been lifted to a λ-body and there
    ; are no transitive references.
    (~> (more ()                                     ; Transitive
              ((ca_i x_i) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := l))

        (done (ca_ul : ca_lr) := (MAP (λ (x_c x_r x_i ...) l) (extd (ca_ul0 : ca_lr0) (ca_ul : ca_lr)) ...))

        (where (ca_ul0 ...) ((lookup ca_i ca_ul) ...))
        (where (ca_lr0 ...) ((lookup ca_i ca_lr) ...))
        synth-map)

    ; synth-prefix: The expression has been lifted to a λ-body and
    ; there are transitive references.
    (~> (more ((ca_t x_t) ...)                       ; Transitive
              ((ca_i x_i) ...)                       ; Intransitive
              (x_c x_r)
              ((ca_ul : ca_lr) := l))
        (done (ca_ul : ca_lr) := (PREFIX (λ (x_c x_r x_t1 x_t2 x_t3 x_i ...) l)
                                         (ca_c0 : ca_c1)
                                         ca_s
                                         (ca_r0 : ca_r1)
                                         (extd (ca_ul0 : ca_lr0) (ca_ul : ca_lr)) ...))

        (where (ca_ul0 ...) ((lookup ca_i ca_ul) ...))
        (where (ca_lr0 ...) ((lookup ca_i ca_lr) ...))
        (where ((ca_t1 x_t1) (ca_t2 x_t2) (ca_t3 x_t3)) (sort&fill ((ca_t x_t) ...))) ; Make sure this holds!

        ; Construct initial row and column address
        (where ca_s (lookup ca_t2 ca_ul))

        (where ca_c0 (lookup ca_t1 ca_ul))
        (where ca_r0 (lookup ca_t3 ca_ul))

        (where ca_c1 (rc (row ca_lr) (column ca_c0)))
        (where ca_r1 (rc (row ca_r0) (column ca_lr)))

        (side-condition (not (empty? (term (ca_t ...)))))
        synth-prefix)))


(define s1 (term (more () () (c r) (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] [2]))))))
(test-equal (redex-match? λ-calc-L c s1) #t)
(test-->> lift s1 (term (done ((rc 1 1) : (rc 2 2)) := (MAP (λ (c r x) (x + x)) ((rc 3 3) : (rc 4 4))))))


(define s2 (term (more () () (c r) (((rc 1 1) : (rc 2 2)) := ((rc [2] [2]) + (rc [2] 5))))))
(test-equal (redex-match? λ-calc-L c s2) #t)
(test-->> lift s2 (term (done ((rc 1 1) : (rc 2 2)) := (MAP (λ (c r x x1) (x + x1))
                                                            ((rc 3 3) : (rc 4 4))
                                                            (HREP ((rc 3 5) : (rc 4 5)) 2)))))

(define s3 (term (more () () (c r) (((rc 2 2) : (rc 10 10)) := (((rc [-1] [-1]) + (rc [-1] [0])) + (rc [0] [-1]))))))
(test-equal (redex-match? λ-calc-L c s3) #t)
(test-->> lift s3 (term (done
                        ((rc 2 2) : (rc 10 10))
                        :=
                        (PREFIX
                         (λ (c r x2 x x1) ((x + x1) + x2))
                         ((rc 2 1) : (rc 10 1))
                         (rc 1 1)
                         ((rc 1 2) : (rc 1 10))))))

(define s4 (term (more () () (c r) (((rc 1 3) : (rc 4 4)) := (SUM ((rc [0] 1) : (rc [0] 2)))))))
(test-equal (redex-match? λ-calc-L c s4) #t)
(test-->> lift
         s4
         (term (done (((rc 1 3) : (rc 4 4)) := (MAP (λ (c r) (SUM (SLICE ((rc 1 1) : (rc 4 2)) c 2 r 2))) 1 2)))))

;; (require pict)
;; (send (pict->bitmap (render-reduction-relation lift)) save-file "/tmp/lift-rules.png" 'png 100)
;; (scale (render-reduction-relation lift) 2)
