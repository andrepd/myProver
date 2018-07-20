open Batteries

open Types
open Util

(* --- *)

(* Negation normal form *)
let rec nnf f =
  match f with
  | Val _ -> failwith "contains bool values"

  | And (x,y) -> And (nnf x , nnf y)
  | Or  (x,y) -> Or  (nnf x , nnf y)
  (* | Imp (x,y) -> Or  (Not (nnf x) , nnf y) *)  (* REEEEEE *)
  | Imp (x,y) -> Or  (nnf (Not x) , nnf y)
  | Iff (x,y) -> Or (And (nnf x , nnf y) , And (nnf (Not x) , nnf (Not y)))
  
  | Not (Not x) -> nnf x
  | Not (And (x,y)) -> Or  (nnf (Not x) , nnf (Not y))
  | Not (Or  (x,y)) -> And (nnf (Not x) , nnf (Not y))
  | Not (Imp (x,y)) -> And (nnf x , nnf (Not y))
  | Not (Iff (x,y)) -> Or (And (nnf x , nnf (Not y)) , And (nnf (Not x) , nnf y))
  
  | Forall (x, p) -> Forall (x, nnf p)
  | Exists (x, p) -> Exists (x, nnf p)
  | Not (Forall (x, p)) -> Exists (x, nnf (Not p))
  | Not (Exists (x, p)) -> Forall (x, nnf (Not p))
  
  | _ -> f

(* Prenex normal form *)
let rec pnf f = 
  let rec aux f = 
    match f with
    | And (Forall (x,p) , Forall (y,q)) -> let z  = variant x $ free_vars f in Forall (z, aux $ And (subst_formula (x |=> Var z) p , subst_formula (y |=> Var z) q))
    | Or  (Exists (x,p) , Exists (y,q)) -> let z  = variant x $ free_vars f in Exists (z, aux $ Or  (subst_formula (x |=> Var z) p , subst_formula (y |=> Var z) q))
 
    | And (Forall (x,p), q) ->             let x' = variant x $ free_vars f in Forall (x', aux $ And (subst_formula (x |=> Var x') p , q))
    | And (q, Forall (x,p)) ->             let x' = variant x $ free_vars f in Forall (x', aux $ And (q , subst_formula (x |=> Var x') p))
    | Or  (Forall (x,p), q) ->             let x' = variant x $ free_vars f in Forall (x', aux $ Or  (subst_formula (x |=> Var x') p , q))
    | Or  (q, Forall (x,p)) ->             let x' = variant x $ free_vars f in Forall (x', aux $ Or  (q , subst_formula (x |=> Var x') p))
 
    | And (Exists (x,p), q) ->             let x' = variant x $ free_vars f in Exists (x', aux $ And (subst_formula (x |=> Var x') p , q))
    | And (q, Exists (x,p)) ->             let x' = variant x $ free_vars f in Exists (x', aux $ And (q , subst_formula (x |=> Var x') p))
    | Or  (Exists (x,p), q) ->             let x' = variant x $ free_vars f in Exists (x', aux $ Or  (subst_formula (x |=> Var x') p , q))
    | Or  (q, Exists (x,p)) ->             let x' = variant x $ free_vars f in Exists (x', aux $ Or  (q , subst_formula (x |=> Var x') p))
 
    | _ -> f
  in
  match f with
  | And (x,y) -> aux $ And (pnf x , pnf y)
  | Or  (x,y) -> aux $ Or  (pnf x , pnf y)
  | Forall (x, p) -> Forall (x, pnf p)
  | Exists (x, p) -> Exists (x, pnf p)
  | _ -> f

(* Skolemization *)
let rec skolem (names: string list) f =
  let aux names fn x y = 
    let (names',  x') = skolem names  x in
    let (names'', y') = skolem names' y in
    (names'', fn x' y')
  in
 
  match f with 
  | Exists (x, p) -> 
    let v = free_vars f in
    let name = variant (if List.is_empty v then "c_"^x else "f_"^x) names in
    let func = Func (name, List.map (fun x -> Var x) v) in
    skolem (name::names) (subst_formula (x |=> func) p)
 
  | Forall (x, p) -> 
    let names', p' = skolem names p in 
    (names', Forall (x, p'))
 
  | And (x,y) -> aux names (fun x y -> And (x,y)) x y
  | Or  (x,y) -> aux names (fun x y -> Or  (x,y)) x y
 
  | _ -> (names, f)

(* Remove leading universal quantifiers *)
let rec specialize f =
  match f with
  | Forall (_, p) -> specialize p
  | _ -> f

(* Skolemization *)
let skolemize (f: 'a formula) : 'a formula =
  (* f |> nnf |> skolem [] |> snd |> pnf |> specialize *)
  f |> nnf |> skolem (List.map fst $ list_functions_formula f) |> snd |> pnf |> specialize
  (* |> tap (fun _ -> print_endline "---")
  |> tap (print_endline % prettyprint_of_formula)
  |> tap (fun _ -> print_endline "---"; print_newline()) *)



let rec cnf f = 
  let rec distrib f = 
    match f with
    | Or (And (x,y) , z) ->
      And (distrib $ Or (x,z) , distrib $ Or (y,z))
    | Or (z , And (x,y)) ->
      And (distrib $ Or (z,x) , distrib $ Or (z,y))
    | _ -> f
  in
  match f with
  | Or (x,y) -> distrib $ Or (cnf x , cnf y)
  | And (x,y) -> And (cnf x , cnf y)
  | _ -> f

let rec setify f = 
  let rec clausify f = 
    match f with
    | Or (x,y) -> clausify x @ clausify y
    |      Atom x  -> [{sign=true;  lit=x}]
    | Not (Atom x) -> [{sign=false; lit=x}]
    | _ -> failwith "Not in cnf"
  in
  match f with
  | And (x,y) -> setify x @ setify y
  | _ -> [clausify f]

let clausify x = 
  x |> cnf |> setify




(* let clausify_opt x =
  let rec step_or f = 
    match f with
    | Or (x,y) -> step_or x @ step_or y
    | _ -> clausify f
  in
  let rec step_forall f = 
    match f with
    | Forall (x,p) -> step_forall p
    | _ -> step_or f
  in
  let rec step_and f = 
    match f with
    | And (x,y) -> step_and x @ step_and y
    | _ -> step_forall f
  in
  step_and x *)
