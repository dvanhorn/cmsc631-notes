#lang racket
(require redex/reduction-semantics)

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

(define a
  (reduction-relation
   A
   (--> (Pred i) ,(sub1 (term i)) pred)
   (--> (Succ i) ,(add1 (term i)) succ)
   (--> (Plus i j) ,(+ (term i) (term j)) plus)
   (--> (Mult i j) ,(* (term i) (term j)) mult)))

(define -->a
  (reduction-relation
   A
   #:domain e
   (--> (in-hole E (Pred i)) (in-hole E ,(sub1 (term i))))
   (--> (in-hole E (Succ i)) (in-hole E ,(add1 (term i))))
   (--> (in-hole E (Mult i j)) (in-hole E ,(* (term i) (term j))))
   (--> (in-hole E (Plus i j)) (in-hole E ,(+ (term i) (term j))))))


#;
(traces (compatible-closure a A e) 
        (term (Mult (Plus (Succ 2) (Mult 2 2))
                    (Plus 5 5))))

;; ,(+ (term v_1)  (term v_2)))))

;; one-step reduction
(define ->a (compatible-closure a A e))


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

(define-judgment-form A
  #:mode (evalr I O)
  [(evalr v v)]
  [(evalr e v)
   -----------
   (evalr (Pred e) ,(sub1 (term v)))]
  [(evalr e v)
   -----------
   (evalr (Succ e) ,(sub1 (term v)))]  
  [(evalr e_1 v_1)
   (evalr e_2 v_2)
   ---------------
   (evalr (Plus e_1 e_2) ,(+ (term v_1) (term v_2)))]
  [(evalr e_1 v_1)
   (evalr e_2 v_2)
   ---------------
   (evalr (Mult e_1 e_2) ,(* (term v_1) (term v_2)))])


   


#;
(redex-check A e 
             (let ((r1 (apply-reduction-relation* -->a (term e)))
                   (r2 (term (eval e))))
               (equal? (first r1) r2)))
                        

  