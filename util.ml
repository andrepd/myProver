open Batteries

open Types

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

let rec free_vars (f: 'a formula) = 
  let rec fv_term t =
    match t with
    | Var x -> [x]
    | Func (_, args) -> List.concat $ List.map fv_term args
  in
  let rec fv_formula f =
    match f with
    | Val _ -> []
    | Atom (Pred (_, args)) -> List.concat $ List.map fv_term args
    | Not x -> fv_formula x
    | And (x,y) -> fv_formula x @ fv_formula y
    | Or  (x,y) -> fv_formula x @ fv_formula y
    | Imp (x,y) -> fv_formula x @ fv_formula y
    | Iff (x,y) -> fv_formula x @ fv_formula y
    | Forall (x, p) -> List.remove (fv_formula p) x
    | Exists (x, p) -> List.remove (fv_formula p) x
  in
  fv_formula f |> List.sort_unique compare

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
    else (
      let x' = variant x (free_vars p) in
      Forall (x', subst_formula ((x |-> Var x') s) p)
    )
  )
  | Exists (x, p) -> (
    if s x <> Var x then
      failwith "subst_formula: cannot replace bound var"
    else (
      let x' = variant x (free_vars p) in
      Forall (x', subst_formula ((x |-> Var x') s) p)
    )
  )



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
  let status = Unix.close_process_full (out_chan, in_chan, err_chan) in

  (* let process_model s =
    String.split_on_char ' ' s
    (* |> List.map Int.of_string *)
    (* Array.init (List.length l) () *)
    |> List.map (fun x -> Int.of_string x > 0)
    |> Array.of_list
  in *)

  let process_model s =
    let l = String.split_on_char ' ' s in
    let a = Array.make (List.length l) false in
    List.iter (fun x ->
      try
        let x = Int.of_string x in
        let sign = x>0 in
        let lit = abs(x) in
        a.(lit-1) <- sign
      (* with Failure "int_of_string" -> *)
      with Failure _ ->
        ()
    ) l;
    a
  in

  (* print_endline sat;
  print_endline model; *)

  if sat.[0] == 'S' then
    (* Some (process_model @@ String.lchop ~n:12 res) *)
    Some (process_model model)
  else
    None
