#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

;; Syntax
(define-language A
  (e ::= 
     v
     (Pred e)
     (Succ e)
     (Plus e e)
     (Mult e e))
  (v ::= i)
  (i j k ::= integer)  
  (E ::=
     hole
     (Pred E)
     (Succ E)
     (Mult E e)
     (Mult v E)
     (Plus E e)
     (Plus v E)))

;; Natural semantics
(define-metafunction A
  [(eval v) v]
  [(eval (Pred e)) ,(sub1 (term (eval e)))]
  [(eval (Succ e)) ,(add1 (term (eval e)))]  
  [(eval (Plus e_1 e_2)) 
   ,(+ (term (eval e_1))
       (term (eval e_2)))]
  [(eval (Mult e_1 e_2))
   ,(* (term (eval e_1))
       (term (eval e_2)))])

;; Reduction axiom
(define a
  (reduction-relation
   A
   (--> (Pred i) ,(sub1 (term i)) pred)
   (--> (Succ i) ,(add1 (term i)) succ)
   (--> (Plus i j) ,(+ (term i) (term j)) plus)
   (--> (Mult i j) ,(* (term i) (term j)) mult)))

;; One-step reduction
(define ->a (compatible-closure a A e))

;; Standard reduction
(define -->a (context-closure a A E))

;; To test:
;; raco test A.rkt
(module+ test        
  ;; Normalization theorem
  (redex-check 
   A e 
   (equal? (apply-reduction-relation* -->a (term e))
           (list (term (eval e)))))
  
  ;; Standardization theorem [EXPENSIVE]
  (redex-check 
   A e 
   (equal? (apply-reduction-relation*  ->a (term e))
           (apply-reduction-relation* -->a (term e)))))
