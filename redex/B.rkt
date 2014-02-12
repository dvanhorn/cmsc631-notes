#lang racket
(require "A.rkt")
(require redex/reduction-semantics)
(provide (all-defined-out))

(define-extended-language B A
  (e ::= ....
     x
     (Div e e)
     (Eq e e)
     (If e e e))
  (x ::= variable)
  (v ::= .... b)
  (b ::= True False) 
  (ρ ::= ((x v) ...))
  (E ::= ....
     (Div E e)
     (Div v E)
     (Eq E e)
     (Eq v E)
     (If E e e)))

(define (b ρ)
  (union-reduction-relations 
   (extend-reduction-relation a B)
   (reduction-relation
    B
    (--> x v (where v (lookup ,ρ x)))
    (--> (Div i j) ,(quotient (term i) (term j))
         (side-condition (not (zero? (term j)))))    
    (--> (Eq i i) True)
    (--> (Eq i j) False
         (side-condition (not (= (term i) (term j)))))    
    (--> (If True e_1 e_2) e_1)
    (--> (If False e_1 e_2) e_2))))

(define (->b ρ)
  (compatible-closure (b ρ) B e))

(define (-->b ρ)
  (context-closure (b ρ) B E))

(define-metafunction B
  pukool : ρ x -> v or #f
  [(pukool ((x_0 v_0) ... (x v)) x) v]
  [(pukool ((x_0 v_0) ... (x_1 v_1)) x)
   (pukool ((x_0 v_0) ...) x)]
  [(pukool () x) #f])

(test-equal (term (pukool ((x 1) (x 5)) x))
            (term 5))

(define-metafunction B
  lookup : ρ x -> v or #f
  [(lookup ((x v) (x_0 v_0) ...) x) v]
  [(lookup ((x_0 v_0) (x_1 v_1) ...) x) 
   (lookup ((x_1 v_1) ...) x)]
  [(lookup () x) #f])


(test-equal (term (lookup ((x 1) (x 5)) x))
            (term 1))

(module+ test
  (test-->> (->b '{(x 4)})
            (term (Mult (Div 5 3) x))
            (term 4))
  (test-->> (->b '{})
            (term (If (Eq 1 3) 5 4))
            (term 4))
  (test-->> (->b '{})
            (term (If (Eq 1 1) 5 4))
            (term 5))
  
  (test-->> (-->b '{(x 4)})
            (term (Mult (Div 5 3) x))
            (term 4))
  (test-->> (-->b '{})
            (term (If (Eq 1 3) 5 4))
            (term 4))
  (test-->> (-->b '{})
            (term (If (Eq 1 1) 5 4))
            (term 5)))

(define-extended-language BE B
  (e ::= .... r)
  (r ::= (Err variable))
  (a ::= v r))
 
(define err
  (reduction-relation 
   BE
   (--> (Div i 0) (Err Div0))
   (--> (Div b v) (Err Div1))
   (--> (Div v b) (Err Div2))
   (--> (Eq b v) (Err Eq1))
   (--> (Eq v b) (Err Eq2))
   (--> (If i e_1 e_2) (Err If))))

(define prop
  (reduction-relation
   BE
   (--> (Pred r) r)
   (--> (Succ r) r)
   (--> (Plus r e) r)
   (--> (Plus v r) r)
   (--> (Mult r e) r)
   (--> (Mult v r) r)
   (--> (Div r e) r)
   (--> (Div v r) r)    
   (--> (Eq r e) r)
   (--> (Eq v r) r)
   (--> (If r e_0 e_1) r)))

(define (bep ρ)
  (union-reduction-relations 
   (extend-reduction-relation (b ρ) BE)
   err prop))

(define (->bep ρ)
  (compatible-closure (bep ρ) BE e))

(define (-->bep ρ)
  (context-closure (bep ρ) BE E))

(module+ test
  (test-->> (->bep '{(x 4)})
            (term (Mult (Div 5 3) x))
            (term 4))
  (test-->> (->bep '{})
            (term (If (Eq 1 3) 5 4))
            (term 4))
  (test-->> (->bep '{})
            (term (If (Eq 1 1) 5 4))
            (term 5))
  
  (test-->> (-->bep '{(x 4)})
            (term (Mult (Div 5 3) x))
            (term 4))
  (test-->> (-->bep '{})
            (term (If (Eq 1 3) 5 4))
            (term 4))
  (test-->> (-->bep '{})
            (term (If (Eq 1 1) 5 4))
            (term 5))
    
  (test-->> (->bep '{(x 4)})
            (term (Mult (Div 5 0) x))
            (term (Err Div0)))
  (test-->> (->bep '{})
            (term (If (Eq 1 True) 5 4))
            (term (Err Eq2)))
  (test-->> (->bep '{})
            (term (If (Div 1 1) 5 4))
            (term (Err If))))