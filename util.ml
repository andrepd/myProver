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
  let Pred (name, args) = f in Pred (name, List.map (subst_term s) args)

let subst_literal (s: 'a -> 'a term) ({sign; lit}: 'a literal) = 
  {sign; lit=subst_atom s lit}

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

(* let prop_numbering (x: 'a clauseset) : int LazyList.t LazyList.t * (int*int) = *)
let prop_numbering (x: 'a clauseset) : int List.t List.t * (int*int) =
  let store = ref @@ Map.empty in
  let num = ref 1 in
  
  let clauses = 
    List.map (fun clause ->
      List.map (fun {sign;lit} -> 
        let n =
          try
            Map.find lit !store
          with
            Not_found -> (
              store := Map.add lit !num !store;
              incr num;
              !num-1
            )
        in
        if sign then
          n
        else
          -n
      ) clause
    ) x
  in
  (clauses, (!num-1, List.length clauses))

(* let numbering_to_pcnf (x: int List.t List.t * (int*int)) : string = *)
let numbering_to_pcnf ((clauses,(nvars,nclauses)): int List.t List.t * (int*int)) : string =
  let body = ref "" in
  List.iter (fun clause ->
    List.iter (fun n -> 
      body := !body ^ Int.to_string n ^ " "
    ) clause;
    body := !body ^ "0\n"
  ) clauses;
  let header = "p cnf " ^ Int.to_string nvars ^ " " ^ Int.to_string nclauses ^ "\n" in
  header ^ !body
  

let to_pcnf (x: 'a clauseset) : string =
  x |> prop_numbering |> numbering_to_pcnf

let call_sat_solver (str: string) : pmodel option =
  if dbg_flag then begin  
  debug_endline "FILE";
  debug_string str;
  debug_endline "ENDFILE";
  end;
  (* let in_descr = Unix.descr_of_in_channel @@ IO.input_string str in
  let out_descr = Unix.descr_of_out_channel @@ IO.output_string () in
  let pid = Unix.create_process "./sat" [||] in_descr out_descr Unix.stderr in *)
  let out_chan, in_chan, err_chan = Unix.open_process_full "./sat" [||] in
  IO.nwrite in_chan str;
  IO.flush in_chan;
  (* IO.read out_chan = 'S' *)
  (* let sat = IO.nread out_chan (1024*4) in *)
  let sat = IO.read_all out_chan in
  (* let model = IO.nread err_chan (1024*4) in *)
  let model = IO.read_all err_chan in
  (* let status = Unix.close_process_full (out_chan, in_chan, err_chan) in *)

  let process_model s =
    let l = String.split_on_char ' ' s |> List.map String.trim |> List.filter (neg String.is_empty) in
    (* debug_int (List.length l); *)
    let a = Array.make (List.length l) false in
    List.iter (fun x ->
      try
        let x = Int.of_string x in
        let sign = x>0 in
        let lit = abs(x) in
        a.(lit-1) <- sign
      with Failure _ ->
        ()
    ) l;
    a
  in

  if dbg_flag then begin
  debug_endline sat;
  end;
  if sat.[0] == 'S' then (
    if dbg_flag then begin
    debug_string model
    end;
    Some (process_model model)
  ) else
    None



let rec list_functions_term (t: 'a term) : ('a * int) list =
  match t with
  | Var x -> []
  | Func (name, args) -> (name, List.length args) :: (List.concat @@ List.map list_functions_term args)

let list_functions_clauseset (x: 'a clauseset) : ('a * int) list =
  (* List.sort_unique compare @@ *)
  List.concat @@ List.map (
    fun {sign;lit=Pred(_,args)} -> List.concat @@ List.map list_functions_term args  
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
    fun {sign;lit=Pred(name,args)} -> (name, List.length args)
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
