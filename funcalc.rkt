#lang racket

(require redex)

(define-language mini-calc
  (n ::= real)
  (t ::= string)
  (v ::= n t (err string))
  (i ::= integer)
  (ca ::= (rc i i))
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
  (cv ::= (ca := v))
  (ce ::= (ca := e))
  (S ::= (σ cv ... (ca := E) ce ...)))

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
   (--> (σ cv_1 ... (ca_r := v) cv_2 ... (ca := (in-hole E ca_r)) ce_4 ...)
        (σ cv_1 ... (ca_r := v) cv_2 ... (ca := (in-hole E v))    ce_4 ...)
        ref-v)

   ;; Cell-reference look-up: reference not yet computed, sort one step!
   (--> (σ cv_1 ... (ca := (in-hole E ca_r)) ce_2 ... (ca_r := e) ce_3 ...)
        (σ cv_1 ... (ca_r := e) (ca := (in-hole E ca_r)) ce_2 ... ce_3 ...)
        ref-e)

   ;; Cell-reference look-up: referenced cell is empty.
   (--> (σ (ca_1 := v) ... (ca := (in-hole E ca_r)) (ca_2 := e) ...)
        (σ (ca_1 := v) ... (ca := (err "#EMPTY"))   (ca_2 := e) ...)
        (side-condition (not (member (term ca_r) (append (term (ca_1 ...)) (term (ca_2 ...))))))
        ref-empty)))


(define s1 (term (σ ((rc 1 1) := (1 + 1)))))
(define s2 (term (σ ((rc 1 1) := (1 + 1))         ((rc 1 2) := (0 = 2)))))
(define s3 (term (σ ((rc 1 1) := (1 + 1))         ((rc 1 2) := (0 = 2)) ((rc 2 1) := (IF (1 = 2) 0 1)))))
(define s4 (term (σ ((rc 1 1) := ((1 + 1) + (rc 1 2))) ((rc 1 2) := 42))))
(define s5 (term (σ ((rc 1 1) := 42)              ((rc 1 2) := (rc 1 1)))))
(define s6 (term (σ ((rc 1 1) := ((rc 1 2) + 1))  ((rc 1 2) := 42))))
(define s7 (term (σ ((rc 1 1) := ((rc 1 2) + 1))  ((rc 1 2) := (41 + 1)))))
(define s8 (term (σ ((rc 1 1) := ((rc 1 3) + 1))  ((rc 1 2) := (41 + 1)))))

(test-equal (redex-match? mini-calc σ s1) #t)
(test-equal (redex-match? mini-calc σ s2) #t)
(test-equal (redex-match? mini-calc σ s3) #t)
(test-equal (redex-match? mini-calc σ s4) #t)
(test-equal (redex-match? mini-calc σ s5) #t)
(test-equal (redex-match? mini-calc σ s6) #t)
(test-equal (redex-match? mini-calc σ s7) #t)
(test-equal (redex-match? mini-calc σ s8) #t)

(apply-reduction-relation* ->mini-calc s1)
(apply-reduction-relation* ->mini-calc s2)
(apply-reduction-relation* ->mini-calc s3)
(apply-reduction-relation* ->mini-calc s4)
(apply-reduction-relation* ->mini-calc s5)
(apply-reduction-relation* ->mini-calc s6)
(apply-reduction-relation* ->mini-calc s7)
(apply-reduction-relation* ->mini-calc s8)


(define-extended-language λ-calc mini-calc-S
  (e ::=
     ....
     x
     (ca : ca)
     (e e)
     (MAP e e ...))
  (v ::=
     ....
     [[v ...] ...]
     (λ (x ...) e))
  (x ::= variable-not-otherwise-mentioned)

  (E ::=
     ....
     (E e)
     (v E)
     (MAP E e ...)
     (MAP (λ (x ...) e) v ... E e ...))

  #:binding-forms
  (λ (x ...) e #:refers-to x ...))
