#lang racket

(require redex)
(require "funcalc.rkt")


;; mini-calc tests
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

(define s12 (term (σ ((rc 2 3) := (MAP (λ (x y) (x + y)) ((rc 1 1) : (rc 2 2)) ((rc 1 1) : (rc 2 2))))
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
