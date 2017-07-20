#lang racket

(require redex
         "mini-calc.rkt")

(provide (all-defined-out))


(define-extended-language λ-calc mini-calc
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

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...)))


(define-union-language λ-calc-S0 λ-calc mini-calc-S)
(define-extended-language λ-calc-S λ-calc-S0
  (E ::=
     ....
     (f ... E e ...)
     [[v ...] ... [v ... E e ...] [e ...] ...] ; For evaluating arrays.
     (MAP v ... E e ...)))


(define-metafunction λ-calc
  rows : v -> i
  [(rows [[v ...] ...]) ,(length (term [[v ...] ...]))]
  [(rows _) (err "#ArgType")])


(define-metafunction λ-calc
  cols : v -> i
  [(cols [[v_1 ...] ... [v_2 ...] [v_3 ...] ...]) ,(length (term [v_2 ...]))]
  [(cols _) (err "#ArgType")])


(define (unpack/racket r_min r_max c_min c_max)
  (term ,(for/list [(r (in-range r_min (add1 r_max)))]
           (term ,(for/list [(c (in-range c_min (add1 c_max)))]
                    (term (rc ,r ,c)))))))

(define-metafunction λ-calc-S
  unpack : (ca : ca) ca -> e
  [(unpack (ca_1 : ca_2) ca)
   ,(unpack/racket (term i_r1) (term i_r2) (term i_c1) (term i_c2))
   (where (rc i_r1 i_c1) (lookup ca_1 ca))
   (where (rc i_r2 i_c2) (lookup ca_2 ca))])


(define-metafunction λ-calc-S
  substitute/rec : e (x ...) (v ...) -> e
  [(substitute/rec e () ()) e]
  ;; [(substitute/rec e (x ...) ()) (err "#ArgCount")]
  ;; [(substitute/rec e () (v ...)) (err "#ArgCount")]
  [(substitute/rec e (x_1 x_2 ..._1) (v_1 v_2 ..._1))
   (substitute/rec (substitute e x_1 v_1) (x_2 ...) (v_2 ...))])


(define ->λ-calc
  (extend-reduction-relation ->mini-calc λ-calc-S
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


(define-metafunction λ-calc
  free-vars-in : e -> (x ...)
  [(free-vars-in x)                x]
  [(free-vars-in (e_1 + e_2))      ,(append (term (free-vars-in e_1)) (term (free-vars-in e_2)))]
  [(free-vars-in (e_1 = e_2))      ,(append (term (free-vars-in e_1)) (term (free-vars-in e_2)))]
  [(free-vars-in (e_1 e_2 ...))    ,(append (term (free-vars-in e_1)) (term (free-vars-in (e_2 ...))))]
  [(free-vars-in (λ (x ...) e_1))  ,(remove* (term (x ...)) (term (free-vars-in e_1)))]
  [(free-vars-in (IF e_1 e_2 e_3)) ,(append (term (free-vars-in e_1))
                                            (term (free-vars-in e_2))
                                            (term (free-vars-in e_3)))]
  [(free-vars-in _) ()])


(define-metafunction λ-calc
  enumerate : (ca : ca) -> (ca ...)
  [(enumerate ((rc i_r1 i_c1) : (rc i_r2 i_c2)))
   ,(flatten
     (build-list
      (- (term i_r2) (term i_r1))
      (λ (r) (build-list
              (- (term i_c2) (term i_c1))
              (λ (c)
                (term (rc ,(+ (term i_r1) r) ,(+ (term i_c1) c))))))))])


(define (in?/racket ca cas)
  (case cas
    ['()  #f]
    [else (if (member (term (lookup ca ,(first cas))) cas)
           #t
           (in?/racket ca (rest cas)))]))
