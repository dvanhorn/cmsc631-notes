type arith = 
    Int of int
  | Pred of arith
  | Succ of arith
  | Mult of arith * arith 
  | Plus of arith * arith
		 
type ecxt = 
    Hole
  | EPred of ecxt
  | ESucc of ecxt
  | EPlusL of ecxt * arith
  | EPlusR of int * ecxt
  | EMultL of ecxt * arith
  | EMultR of int * ecxt
	
let rec plug (c : ecxt) (e : arith) : arith =
  match c with
      Hole -> e
    | EPred c -> Pred (plug c e)
    | ESucc c -> Succ (plug c e)
    | EPlusL (c, e') -> Plus (plug c e, e')
    | EPlusR (i, c) -> Plus (Int i, plug c e)
    | EMultL (c, e') -> Mult (plug c e, e')
    | EMultR (i, c) -> Mult (Int i, plug c e)
	
let rec reduce (e : arith) : arith option =
  match e with
      Pred (Int i) -> Some (Int (i-1))
    | Succ (Int i) -> Some (Int (i+1))
    | Plus (Int i, Int j) -> Some (Int (i*j))
    | Mult (Int i, Int j) -> Some (Int (i*j))
    | _ -> None 
	
let rec decompose (e : arith) : (ecxt * arith) option =
  match e with
      Int i -> None
    | Pred (Int i) -> Some (Hole, e)
    | Succ (Int i) -> Some (Hole, e)
    | Plus (Int i, Int j) -> Some (Hole, e)
    | Mult (Int i, Int j) -> Some (Hole, e)
    | Pred e -> 
	let Some (c', e') = decompose e in Some (EPred c', e')
    | Succ e -> 
	let Some (c', e') = decompose e in Some (ESucc c', e')
    | Plus (Int i, e) -> 
	let Some (c', e') = decompose e in Some (EPlusR (i, c'), e')
    | Plus (e, e2) ->
	let Some (c', e') = decompose e in Some (EPlusL (c', e2), e')
    | Mult (Int i, e) -> 
	let Some (c', e') = decompose e in Some (EMultR (i, c'), e')
    | Mult (e, e2) ->
	let Some (c', e') = decompose e in Some (EMultL (c', e2), e')
					     
let rec eval (e : arith) : int =
  match e with
      Int i -> i
    | _ -> 
	let Some (c, e) = decompose e in
	let Some r = reduce e in
	  eval (plug c r)
	    
let test e1 e2 name = 
  if e1 = e2 then () else raise (Failure name)
    
let _ = test (plugc (EPred Hole) (ESucc Hole)) (EPred (ESucc Hole)) "plugc"
  
let _ = test (decompose (Succ (Int 3))) 
  (Some (Hole, (Succ (Int 3)))) 
  "triv"
  
let _ = test (decompose (Pred (Succ (Int 3))))
  (Some (EPred Hole, Succ (Int 3)))
  "pred"
  
let _ = test 
  (decompose (Succ (Pred (Succ (Int 3)))))
  (Some (ESucc (EPred Hole), Succ (Int 3)))
  "succ-pred"
  
let _ = test
  (decompose (Mult (Succ (Pred (Succ (Int 3))), Int 5))) 
  (Some (EMultL (ESucc (EPred Hole), Int 5), Succ (Int 3)))
  "multl-succ-pred"
  
let _ = test
  (decompose (Mult (Int 5, (Succ (Pred (Succ (Int 3)))))))
  (Some (EMultR (5, (ESucc (EPred Hole))), Succ (Int 3)))
  "multr-succ-pred"
  
let _ = test
  (eval (Mult (Int 5, (Succ (Pred (Succ (Int 3)))))))
  (5*(((3+1)-1)+1))
  "eval"
  
(* let _ = test (decompose (Pred (Succ 3)) Hole) *)
