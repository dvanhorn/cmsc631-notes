type iexp = 
  | E_Ref of iexp
  | E_Deref of iexp
  | E_Update of iexp * iexp
  | E_Seq of iexp * iexp
  | E_Int of int
  | E_Bool of bool
  | E_Var of string
  | E_Pred of iexp
  | E_Succ of iexp
  | E_Plus of iexp * iexp
  | E_Mult of iexp * iexp
  | E_Div of iexp * iexp
  | E_If of iexp * iexp * iexp
  | E_App of iexp * iexp
  | E_Fun of string * iexp

type ans =
    A_Val of value * sto
  | A_Err of string
and sto = (int * value) list
and value =
  | V_Ref of int 
  | V_Int of int
  | V_Bool of bool
  | V_Fun of string * iexp * env
and env = (string * value) list

type cont =
  | K_Mt
  | K_Ref of cont
  | K_Deref of cont
  | K_UpdateL of iexp * env * cont
  | K_UpdateR of value * cont
  | K_SeqL of iexp * env * cont
  | K_SeqR of value * cont
  | K_AppL of iexp * env * cont
  | K_AppR of value * cont
  | K_Pred of cont
  | K_Succ of cont
  | K_PlusL of iexp * env * cont
  | K_PlusR of value * cont
  | K_MultL of iexp * env * cont
  | K_MultR of value * cont
  | K_DivL of iexp * env * cont
  | K_DivR of value * cont
  | K_If of iexp * iexp * env * cont
 

exception Unbound of string
exception Illegal_Ref
exception Not_Implemented

let rec lookup (r : env) (x : string) : value =
  match r with
      [] -> raise (Unbound x)
    | (y,v)::r -> if (x = y) then v else lookup r x

let rec allocate (s : sto) : int =
  match s with
    | [] -> 0
    | ((l,v)::s) ->
	(allocate s) + 1

let rec sto_lookup (s : sto) (i : int) : value =
  match s with
    | [] -> raise Illegal_Ref
    | (j,v)::s ->
	if (j=i) then v else sto_lookup s i

let rec sto_update (s : sto) (i : int) (v : value) : sto =
  match s with
    | [] -> raise Illegal_Ref
    | (j,v1)::s ->
	if (j=i) then (j,v)::s else (j,v1)::(sto_update s i v)


let rec ev (e : iexp) (r : env) (s : sto) (k : cont) : ans =
  match e with
    | E_Ref e -> ev e r s (K_Ref k)
    | E_Deref e -> ev e r s (K_Deref k)
    | E_Update (e1, e2) -> ev e1 r s (K_UpdateL (e2, r, k))
    | E_Seq (e1, e2) -> ev e1 r s (K_SeqL (e2, r, k))
    | E_Int i -> co k (V_Int i) s
    | E_Bool b -> co k (V_Bool b) s
    | E_Var x -> co k (lookup r x) s
    | E_Pred e -> ev e r s (K_Pred k)
    | E_Succ e -> ev e r s (K_Succ k)
    | E_Plus (e1, e2) -> ev e1 r s (K_PlusL (e2, r, k))
    | E_Mult (e1, e2) -> ev e1 r s (K_MultL (e2, r, k))
    | E_Div (e1, e2) -> ev e1 r s (K_DivL (e2, r, k))
    | E_If (e1, e2, e3) -> ev e1 r s (K_If (e2, e3, r, k))
    | E_App (e1, e2) -> ev e1 r s (K_AppL (e2, r, k))
    | E_Fun (x, e) -> co k (V_Fun (x, e, r)) s
and co (k : cont) (v : value) (s : sto) : ans =
  match k with
    | K_Mt -> A_Val (v, s)
    | K_Ref k -> 
	let l = allocate s in
	  co k (V_Ref l) ((l,v)::s)
    | K_Deref k ->
	(match v with
	  | V_Ref i -> co k (sto_lookup s i) s
	  | _ -> A_Err "not a reference")
    | K_UpdateL (e, r, k) -> ev e r s (K_UpdateR (v, k))
    | K_UpdateR (v1, k) -> 
	(match v1 with
	  | V_Ref i -> co k v1 (sto_update s i v)
	  | _ -> A_Err "not a reference")
    | K_SeqL (e, r, k) -> ev e r s (K_SeqR (v, k))	
    | K_SeqR (v1, k) -> co k v1 s
    | K_AppL (e, r, k) -> ev e r s (K_AppR (v, k))
    | K_AppR (f, k) ->
	(match f with
	   | V_Fun (x, e, r) -> ev e ((x,v)::r) s k
	   | _ -> A_Err "not a function")
    | K_Pred k ->
	(match v with
	   | V_Int i -> co k (V_Int (i-1)) s
	   | _ -> A_Err "not an integer")
    | K_Succ k ->
	(match v with
	   | V_Int i -> co k (V_Int (i+1)) s
	   | _ -> A_Err "not an integer")
    | K_PlusL (e, r, k) -> ev e r s (K_PlusR (v, k))
    | K_PlusR (u, k) -> 
	(match (u, v) with
	   | (V_Int i, V_Int j) -> co k (V_Int (i+j)) s
	   | _ -> A_Err "not an integer")
    | K_MultL (e, r, k) -> ev e r s (K_MultR (v, k))
    | K_MultR (u, k) -> 
	(match (u, v) with
	   | (V_Int i, V_Int j) -> co k (V_Int (i*j)) s
	   | _ -> A_Err "not an integer")
    | K_DivL (e, r, k) -> ev e r s (K_DivR (v, k))
    | K_DivR (u, k) -> 
	(match (u, v) with
	   | (V_Int i, V_Int 0) -> A_Err "div by zero"
	   | (V_Int i, V_Int j) -> co k (V_Int (i/j)) s
	   | _ -> A_Err "not an integer")
    | K_If (e2, e3, r, k) ->
	(match v with
	   | V_Bool true -> ev e2 r s k
	   | V_Bool false -> ev e3 r s k
	   | _ -> A_Err "not a boolean")

let eval e = ev e [] [] K_Mt

let two = E_Fun ("s", E_Fun ("z", E_App (E_Var "s", E_App (E_Var "s", E_Var "z"))))
let succ = E_Fun ("x", (E_Succ (E_Var "x")))
let do_256 = E_App (two, (E_App (two, E_App (two, two))))
let v1 = eval (E_App (E_App (do_256, succ), E_Int 0))

let succ_bang = E_Fun("b", E_Update (E_Var "b", E_Succ (E_Deref (E_Var "b"))))
let v2 = eval (E_App (E_App (do_256, succ_bang), (E_Ref (E_Int 0))))




