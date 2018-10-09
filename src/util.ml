open Batteries

open Types

open Debug

let ($) = (@@)

let (|=>) a b x = 
  if x = a then b else Var x

let (|->) a b f x = 
  if x = a then b else f x

(* --- *)

let rec variant x l =
  if List.mem x l then 
    variant (x^"'") l
  else
    x 

let vars_term (t: 'a term) =
  let rec aux t =
    match t with
    | Var x -> [x]
    | Func (_, args) -> List.concat $ List.map aux args
  in 
  List.sort_unique compare @@ aux t

let vars (f: 'a formula) =
  let rec aux f =
    match f with
    | Val _ -> []
    | Atom (Pred (_, args)) -> List.concat $ List.map vars_term args
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) -> 
      aux x @ aux y
    | Forall (x, p) | Exists (x, p) -> 
      List.cons x (aux p)
  in
  List.sort_unique compare @@ aux f

let rec free_vars (f: 'a formula) = 
  let rec aux f =
    match f with
    | Val _ -> []
    | Atom (Pred (_, args)) -> List.concat $ List.map vars_term args
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) -> 
      aux x @ aux y
    | Forall (x, p) | Exists (x, p) -> 
      (* List.remove (aux p) x *)
      List.remove (free_vars p) x  (* ######################## *)
  in
  aux f |> List.sort_unique compare

(* --- *)

let rec subst_term (s: 'a -> 'a term) (f: 'a term) =
  match f with
  | Var x -> s x
  | Func (name, args) -> Func (name, List.map (subst_term s) args)

let subst_atom (s: 'a -> 'a term) (f: 'a atom) =
  match f with
  | Pred (name, args) -> Pred (name, List.map (subst_term s) args)

let subst_literal (s: 'a -> 'a term) ({sign; atom}: 'a literal) = 
  {sign; atom=subst_atom s atom}

let subst_clause (s: 'a -> 'a term) (f: 'a clause) =
  List.map (subst_literal s) f

let subst_clause_set (s: 'a -> 'a term) (f: 'a clauseset) =
  List.map (subst_clause s) f

let rec subst_formula (s: 'a -> 'a term) (f: 'a formula) =
  let needs_rename x p = 
    List.exists (fun y -> List.mem x (vars_term $ s y)) (free_vars $ Forall (x,p))
  in
  match f with 
  | Val _ -> f
  | Atom x -> Atom (subst_atom s x)
  | Not x -> Not (subst_formula s x)
  | And (x,y) -> And (subst_formula s x, subst_formula s y)
  | Or  (x,y) -> Or  (subst_formula s x, subst_formula s y)
  | Imp (x,y) -> Imp (subst_formula s x, subst_formula s y)
  | Iff (x,y) -> Iff (subst_formula s x, subst_formula s y)
  | Forall (x, p) -> (
    if s x <> Var x then
      failwith "subst_formula: cannot replace bound var"
    else if needs_rename x p then (
      let x' = variant x (free_vars p) in
      Forall (x', subst_formula ((x |-> Var x') s) p)
    ) else (
      Forall (x, subst_formula s p)
    )
  )
  | Exists (x, p) -> (
    if s x <> Var x then
      failwith "subst_formula: cannot replace bound var"
    else if needs_rename x p then (
      let x' = variant x (free_vars p) in
      Exists (x', subst_formula ((x |-> Var x') s) p)
    ) else (
      Exists (x, subst_formula s p)
    )
  )



(* --- *)

let rec list_functions_term (t: 'a term) : ('a * int) list =
  match t with
  | Var x -> []
  | Func (name, args) -> (name, List.length args) :: (List.concat @@ List.map list_functions_term args)

let list_functions_clauseset (x: 'a clauseset) : ('a * int) list =
  (* List.sort_unique compare @@ *)
  List.concat @@ List.map (
    fun {sign;atom=Pred(_,args)} -> List.concat @@ List.map list_functions_term args  
  ) (List.concat x)

let list_functions_formula (x: 'a formula) : ('a * int) list =
  let rec aux (f: 'a formula) : ('a * int) list =
    match f with
    | Val x -> []
    | Atom (Pred (name, args)) -> List.concat @@ List.map list_functions_term args
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) ->
      aux x @ aux y
    | Forall (x, p) | Exists (x, p) ->
      aux p
  in
  (* List.sort_unique compare @@  *)
  aux x

let list_predicates_clauseset (x: 'a clauseset) : ('a * int) list =
  (* List.sort_unique compare @@ *)
  List.map (
    fun {sign;atom=Pred(name,args)} -> (name, List.length args)
  ) (List.concat x)

let rec list_predicates_formula (f: 'a formula) : ('a * int) list =
  let rec aux (f: 'a formula) : ('a * int) list =
    match f with
    | Val x -> []
    | Atom (Pred (name, args)) -> [(name, List.length args)]
    | Not x -> aux x
    | And (x,y) | Or (x,y) | Imp (x,y) | Iff (x,y) ->
      aux x @ aux y
    | Forall (x, p) | Exists (x, p) ->
      aux p
  in
  (* List.sort_unique compare @@  *)
  aux f



(** Encode a string clauseset to an int clauseset *)
let encode_clauseset (x: string clauseset) : int clauseset =
  let table = ref Map.empty in
  let num = ref 1 in
  let table_var = ref Map.empty in
  let num_var = ref (-1) in

  let get_num (s: string) : int =
    try
      Map.find s !table
    with
      Not_found -> (
        table := Map.add s !num !table;
        let r = !num in
        incr num;
        r
      )
  in

  let get_num_var (s: string) : int =
    try
      Map.find s !table_var
    with
      Not_found -> (
        table_var := Map.add s !num_var !table_var;
        let r = !num_var in
        num_var := !num_var - 2;
        r
      )
  in

  let rec encode_term (x: string term) : int term =
    match x with
    | Var x -> 
      Var (get_num_var x)
    | Func (name, args) ->
      Func (get_num name, List.map encode_term args)
      
  in

  let encode_atom (x: string atom) : int atom =
    let Pred (name, args) = x in
    Pred (get_num name, List.map encode_term args)
  in

  List.map (fun clause ->
    let r = List.map (fun {sign;atom} -> 
      {sign; atom = encode_atom atom}
    ) clause in
    table_var := Map.empty;
    num_var := -1;
    r
  ) x

let reencode_clause (clause: int clause) : int clause =
  let table_var = ref Map.empty in
  let num_var = ref (-1) in

  let get_num_var (s: int) : int =
    try
      Map.find s !table_var
    with
      Not_found -> (
        table_var := Map.add s !num_var !table_var;
        let r = !num_var in
        num_var := !num_var - 2;
        r
      )
  in

  let rec encode_term (x: int term) : int term =
    match x with
    | Var x -> 
      Var (get_num_var x)
    | Func (name, args) ->
      Func (name, List.map encode_term args)
      
  in

  let encode_atom (x: int atom) : int atom =
    let Pred (name, args) = x in
    Pred (name, List.map encode_term args)
  in

  List.map (fun {sign;atom} -> 
    {sign; atom = encode_atom atom}
  ) clause
    
let reencode_clauseset (x) = 
  List.map reencode_clause x



let string_of_int_subst (s: (int, int term) Map.t) =
  let pair_to_string (a,b) = 
    Int.to_string a ^ "/" ^ string_of_int_term b
  in
  String.concat ", " (List.of_enum @@ map pair_to_string (Map.enum s))

let rec list_vars_term x =
  match x with
  | Var y -> Enum.singleton y
  | Func (_, args) -> Enum.concat_map list_vars_term (List.enum args)

let list_vars_literal {atom} =
  match atom with
  | Pred (_, args) -> Enum.concat_map list_vars_term (List.enum args)

let list_vars_clause x =
  Enum.concat_map list_vars_literal (List.enum x)
