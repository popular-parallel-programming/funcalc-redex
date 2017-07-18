#lang racket

(require redex)

(define-language mini-calc
  (n ::= real)
  (i ::= integer)
  (t ::= string)
  (v ::= n t (err string))
  (ca ::=
      (rc  i   i)   ; absolute
      (rc [i]  i)   ; row-relative
      (rc  i  [i])  ; column-relative
      (rc [i] [i])) ; relative
  ;; Formula expressions.
  (e ::=
     v
     ca
     (e + e)
     (e = e)
     (IF e e e))
  ;; A sheet whose cells reduce from expressions to values.
  (s ::= (σ (ca := e) ...)))

(define-extended-language mini-calc-S mini-calc
  (E ::=
     hole
     (E + e)
     (v + E)
     (E = e)
     (v = E)
     (IF E e e))
  (S ::= (σ (ca_v := v) ... (ca := E) (ca_e := e) ...)))


(define-metafunction mini-calc
  lookup : ca ca -> ca
  [(lookup (rc [i_1]  i_2)  (rc i_3 _))   (rc ,(+ (term i_1) (term i_3)) i_2)]
  [(lookup (rc  i_1  [i_2]) (rc _ i_4))   (rc i_1                        ,(+ (term i_2) (term i_4)))]
  [(lookup (rc [i_1] [i_2]) (rc i_3 i_4)) (rc ,(+ (term i_1) (term i_3)) ,(+ (term i_2) (term i_4)))]
  [(lookup ca _)                          ca])


(define ->mini-calc
  (reduction-relation mini-calc-S
   #:domain s
   (--> (in-hole S (n_1 + n_2))
        (in-hole S ,(+ (term n_1) (term n_2)))
        plus)

   (--> (in-hole S (v_1 = v_1))
        (in-hole S 1)
        eq-tt)
   (--> (in-hole S (v_1 = v_2))
        (in-hole S 0)
        eq-ff)

   (--> (in-hole S (IF 0 e_1 e_2))
        (in-hole S e_2)
        if-tt)
   (--> (in-hole S (IF n e_1 e_2))
        (in-hole S e_1)
        (side-condition (not (zero? (term n))))
        if-ff)

   ;; Cell-reference look-up: reference already computed.
   (--> (σ (ca_1 := v_1) ... (ca_a := v) (ca_2 := v_2) ... (ca := (in-hole E ca_r)) (ca_3 := e_3) ...)
        (σ (ca_1 := v_1) ... (ca_a := v) (ca_2 := v_2) ... (ca := (in-hole E v))    (ca_3 := e_3) ...)
        (where ca_a (lookup ca_r ca))
        ref-v)

   ;; Cell-reference look-up: reference not yet computed, sort one step!
   (--> (σ (ca_1 := v_1) ... (ca := (in-hole E ca_r)) (ca_2 := e_2) ... (ca_a := e) (ca_3 := e_3) ...)
        (σ (ca_1 := v_1) ... (ca_a := e) (ca := (in-hole E ca_r)) (ca_2 := e_2) ... (ca_3 := e_3) ...)
        (where ca_a (lookup ca_r ca))
        ref-e)

   ;; Cell-reference look-up: referenced cell is empty.
   (--> (σ (ca_1 := v) ... (ca := (in-hole E ca_r)) (ca_2 := e) ...)
        (σ (ca_1 := v) ... (ca := (err "#EMPTY"))   (ca_2 := e) ...)
        (where ca_a (lookup ca_r ca))
        (side-condition (not (member (term ca_a) (append (term (ca_1 ...)) (term (ca_2 ...))))))
        ref-empty)))


(define s1 (term (σ ((rc 1 1) := (1 + 1)))))
(define s2 (term (σ ((rc 1 1) := (1 + 1))         ((rc 1 2) := (0 = 2)))))
(define s3 (term (σ ((rc 1 1) := (1 + 1))         ((rc 1 2) := (0 = 2)) ((rc 2 1) := (IF (1 = 2) 0 1)))))
(define s4 (term (σ ((rc 1 1) := ((1 + 1) + (rc 1 2))) ((rc 1 2) := 42))))
(define s5 (term (σ ((rc 1 1) := 42)              ((rc 1 2) := (rc [0] [-1])))))
(define s6 (term (σ ((rc 1 1) := ((rc 1 2) + 1))  ((rc 1 2) := 42))))
(define s7 (term (σ ((rc 1 1) := ((rc 1 2) + 1))  ((rc 1 2) := (41 + 1)))))
(define s8 (term (σ ((rc 1 1) := ((rc [0] [1]) + 1))  ((rc 1 2) := (41 + 1)))))
(define s9  (term (σ ((rc 1 1) := 1) ((rc 1 2) := (1 + (rc 1 1)))
                     ((rc 2 1) := (1 + (rc 1 1))))))
(define s10 (term (σ ((rc 1 1) := 1) ((rc 1 2) := (1 + (rc [0] [-1])))
                     ((rc 2 1) := (1 + (rc [-1] [0]))))))


(test-equal (redex-match? mini-calc s s1)  #t)
(test-equal (redex-match? mini-calc s s2)  #t)
(test-equal (redex-match? mini-calc s s3)  #t)
(test-equal (redex-match? mini-calc s s4)  #t)
(test-equal (redex-match? mini-calc s s5)  #t)
(test-equal (redex-match? mini-calc s s6)  #t)
(test-equal (redex-match? mini-calc s s7)  #t)
(test-equal (redex-match? mini-calc s s8)  #t)
(test-equal (redex-match? mini-calc s s9)  #t)
(test-equal (redex-match? mini-calc s s10) #t)


(test-equal (apply-reduction-relation* ->mini-calc s1)
            '((σ ((rc 1 1) := 2))))
(test-equal (apply-reduction-relation* ->mini-calc s2)
            '((σ ((rc 1 1) := 2) ((rc 1 2) := 0))))
(test-equal (apply-reduction-relation* ->mini-calc s3)
            '((σ ((rc 1 1) := 2) ((rc 1 2) := 0) ((rc 2 1) := 1))))
(test-equal (apply-reduction-relation* ->mini-calc s4)
            '((σ ((rc 1 2) := 42) ((rc 1 1) := 44))))
(test-equal (apply-reduction-relation* ->mini-calc s5)
            '((σ ((rc 1 1) := 42) ((rc 1 2) := 42))))
(test-equal (apply-reduction-relation* ->mini-calc s6)
            '((σ ((rc 1 2) := 42) ((rc 1 1) := 43))))
(test-equal (apply-reduction-relation* ->mini-calc s7)
            '((σ ((rc 1 2) := 42) ((rc 1 1) := 43))))
(test-equal (apply-reduction-relation* ->mini-calc s8)
            '((σ ((rc 1 2) := 42) ((rc 1 1) := 43))))
(test-equal (apply-reduction-relation* ->mini-calc s9)
            '((σ ((rc 1 1) := 1) ((rc 1 2) := 2) ((rc 2 1) := 2))))
(test-equal (apply-reduction-relation* ->mini-calc s10)
            '((σ ((rc 1 1) := 1) ((rc 1 2) := 2) ((rc 2 1) := 2))))


(define-extended-language λ-calc mini-calc-S
  (e ::=
     ....
     x
     (ca : ca) ;  [[v ...] ...] via unpack
     [[e ...] ...] ; TODO: Can we avoid having this?
     (e e)
     (MAP e ...))

  (v ::=
     ....
     [[v ... ] ...]
     (λ (x ...) e))

  (x ::= variable-not-otherwise-mentioned)

  (E ::=
     ....
     (E e ...)
     ((λ (x ...) e) v ... E e ...) ; For evaluating args.
     [[v ...] ... [v ... E e ...] [e ...] ...] ; For evaluating arrays.
     (MAP v ... E e ...))

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...)))


(define (unpack/racket r_min r_max c_min c_max)
  (term ,(for/list [(r (in-range r_min (add1 r_max)))]
           (term ,(for/list [(c (in-range c_min (add1 c_max)))]
                    (term (rc ,r ,c)))))))


(define-metafunction λ-calc
  unpack : (ca : ca) ca -> e
  [(unpack (ca_1 : ca_2) ca)
   ,(unpack/racket (term i_r1) (term i_r2) (term i_c1) (term i_c2))
   (where (rc i_r1 i_c1) (lookup ca_1 ca))
   (where (rc i_r2 i_c2) (lookup ca_2 ca))])


(define ->λ-calc
  (extend-reduction-relation ->mini-calc λ-calc
    #:domain s
    (--> (in-hole S ((λ (x ...) e) v ...))
         (in-hole S (substitute e x ... v ...))
         (side-condition (eq? (length '(x ...)) (length '(v ...))))
         app)

    (--> (σ (ca_v1 := v_1) ... (ca := (in-hole E (ca_1 : ca_2))) (ca_e1 := e_1) ...)
         (σ (ca_v1 := v_1) ... (ca := (in-hole E (unpack (ca_1 : ca_2) ca))) (ca_e1 := e_1) ...)
         unpack)

    (--> (in-hole S (MAP (λ (x) e) [[v ...] ...]))
         (in-hole S [[((λ (x) e) v) ...] ...])
         map)))


;; λ-calc tests
(define s11 (term (σ ((rc 2 3) := ((rc 1 1) : (rc 2 2)))
                     ((rc 1 1) := 1)
                     ((rc 1 2) := (1 + (rc [0] [-1])))
                     ((rc 2 1) := (1 + (rc [-1] [0])))
                     ((rc 2 2) := ((rc [0] [-1]) + (rc [-1] [0]))))))


(test-equal (redex-match? λ-calc s s11) #t)
(test-equal (apply-reduction-relation* ->λ-calc s11) '((σ
                                                        ((rc 1 1) := 1)
                                                        ((rc 1 2) := 2)
                                                        ((rc 2 1) := 2)
                                                        ((rc 2 2) := 4)
                                                        ((rc 2 3) := ((1 2) (2 4))))))

(define s12 (term (σ ((rc 2 3) := (MAP (λ (x) (x + x)) ((rc 1 1) : (rc 2 2))))
                     ((rc 1 1) := 1)
                     ((rc 1 2) := (1 + (rc [0] [-1])))
                     ((rc 2 1) := (1 + (rc [-1] [0])))
                     ((rc 2 2) := ((rc [0] [-1]) + (rc [-1] [0]))))))


(test-equal (redex-match? λ-calc s s12) #t)
(test-equal (apply-reduction-relation* ->λ-calc s12) '((σ
                                                        ((rc 1 1) := 1)
                                                        ((rc 1 2) := 2)
                                                        ((rc 2 1) := 2)
                                                        ((rc 2 2) := 4)
                                                        ((rc 2 3) := ((2 4) (4 8))))))
