#lang typed/racket

(require "typecheck.rkt")

(define symm-ty : Expr
  (Ast->Expr '(forall ([A U]
                       [n A]
                       [m A]
                       [eq (= A n m)])
                      (= A m n))))
(define symm-tm : Expr
  (Ast->Expr '(lambda (A n m eq)
                (ind-= A n m
                       eq
                       (lambda (x eq) (= A x n))
                       (refl A n)))))

(define trans-ty : Expr
  (Ast->Expr '(forall ([A U]
                       [x A]
                       [y A]
                       [z A]
                       [x=y (= A x y)]
                       [y=z (= A y z)])
                      [= A x z])))

(define trans-tm : Expr
  (Ast->Expr '(λ (A x y z x=y y=z)
                (ind-= A y x
                       (symm-ty A x y x=y)
                       (λ (w x=w) (= A w z))
                       y=z))))

(define not-exists->forall-not-ty : Expr
  (Ast->Expr '(forall ([A U]
                       [P (forall ([x A]) U)]
                       [pf (forall ([c (exists ([x A]) (P x))]) Bot)])
                      (forall ([x A])
                              (forall ([_ (P x)]) Bot)))))

(define not-exists->forall-not-tm : Expr
  (Ast->Expr '(λ (A P ex->bot) (λ (x) (λ (px) (ex->bot (intro-ex A P x px)))))))

(time
 (assert (check '() symm-ty 'U))
 (assert (check '() symm-tm symm-ty))
 
 (assert (check '() trans-ty 'U))
 (assert (check `((symm-ty ,symm-ty)) trans-tm trans-ty))

 (assert (check '() not-exists->forall-not-ty 'U))
 (assert (check '() not-exists->forall-not-tm not-exists->forall-not-ty)))