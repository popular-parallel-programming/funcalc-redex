#lang racket

(require redex
         "lambda-calc.rkt")

;; λ-calc tests
(define s1 (term (σ ((rc 2 3) := ((rc 1 1) : (rc 2 2)))
                    ((rc 1 1) := 1)
                    ((rc 1 2) := (1 + (rc [0] [-1])))
                    ((rc 2 1) := (1 + (rc [-1] [0])))
                    ((rc 2 2) := ((rc [0] [-1]) + (rc [-1] [0]))))))


(test-equal (redex-match? λ-calc s s1) #t)
(test-equal (apply-reduction-relation* ->λ-calc s1) '((σ
                                                        ((rc 1 1) := 1)
                                                        ((rc 1 2) := 2)
                                                        ((rc 2 1) := 2)
                                                        ((rc 2 2) := 4)
                                                        ((rc 2 3) := ((1 2) (2 4))))))

(define s2 (term (σ ((rc 2 3) := (MAP (λ (x y) (x + y)) ((rc 1 1) : (rc 2 2)) ((rc 1 1) : (rc 2 2))))
                    ((rc 1 1) := 1)
                    ((rc 1 2) := (1 + (rc [0] [-1])))
                    ((rc 2 1) := (1 + (rc [-1] [0])))
                    ((rc 2 2) := ((rc [0] [-1]) + (rc [-1] [0]))))))


(test-equal (redex-match? λ-calc s s2) #t)
(test-equal (apply-reduction-relation* ->λ-calc s2) '((σ
                                                       ((rc 1 1) := 1)
                                                       ((rc 1 2) := 2)
                                                       ((rc 2 1) := 2)
                                                       ((rc 2 2) := 4)
                                                       ((rc 2 3) := ((2 4) (4 8))))))
