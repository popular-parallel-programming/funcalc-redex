#lang racket

(require redex)

(provide (all-defined-out))

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
        (σ (ca_1 := v) ... (ca := (err "#Empty"))   (ca_2 := e) ...)
        (where ca_a (lookup ca_r ca))
        (side-condition (not (member (term ca_a) (append (term (ca_1 ...)) (term (ca_2 ...))))))
        ref-empty)))


(define-extended-language λ-calc mini-calc-S
  (e ::=
     ....
     x
     (ca : ca) ;  [[v ...] ...] via unpack
     (e e ...)
     (MAP e ...))

  (f ::= (λ (x ...) e))

  (v ::=
     ....
     [[v ... ] ...]
     f)

  (x ::= variable-not-otherwise-mentioned)

  (E ::=
     ....
     (f ... E e ...)
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


(define-metafunction λ-calc
  substitute/rec : e (x ...) (v ...) -> e
  [(substitute/rec e () ()) e]
  [(substitute/rec e (x ...) ()) (err "#ArgCount")]
  [(substitute/rec e () (v ...)) (err "#ArgCount")]
  [(substitute/rec e (x_1 x_2 ..._1) (v_1 v_2 ..._1))
   (substitute/rec (substitute e x_1 v_1) (x_2 ...) (v_2 ...))])


(define-metafunction λ-calc
  rows : v -> i
  [(rows [[v ...] ...]) ,(length (term [[v ...] ...]))]
  [(rows _) (err "#ArgType")])


(define-metafunction λ-calc
  cols : v -> i
  [(cols [[v_1 ...] ... [v_2 ...] [v_3 ...] ...]) ,(length (term [v_2 ...]))]
  [(cols _) (err "#ArgType")])


(define ->λ-calc
  (extend-reduction-relation ->mini-calc λ-calc
    #:domain s
    (--> (in-hole S ((λ (x ..._1) e) v ..._1))
         (in-hole S (substitute/rec e (x ...) (v ...)))
         app)

    (--> (in-hole S ((λ (x_1 ..._1 x_2 x_3 ...) e) v ..._1))
         (in-hole S ((λ (x_2 x_3 ...) (substitute/rec e (x_1 ...) (v ...)))))
         app-part)

    ;; FIXME: These are fixed-arity map. How can I generalize this?
    (--> (in-hole S (MAP f [[v_1 ...] ...]))
         (in-hole S [[(f v_1) ...] ...])
         map1)

    (--> (in-hole S (MAP f [[v_1 ...] ...] [[v_2 ...] ...]))
         (in-hole S [[(f v_1 v_2) ...] ...])
         map2)

    (--> (σ (ca_v1 := v_1) ... (ca := (in-hole E (ca_1 : ca_2))) (ca_e1 := e_1) ...)
         (σ (ca_v1 := v_1) ... (ca := (in-hole E (unpack (ca_1 : ca_2) ca))) (ca_e1 := e_1) ...)
         unpack)))
