open Batteries

open Types
open Unification
open Util

open Debug

let bold x = "\o033[1m" ^ x ^ "\o033[0m"

let sign x = x>0

(* ---- *)

(** Map variables to elem *)
let prop_abstraction (elem: 'a) (x: 'a clauseset) = 
  (* subst_clause_set (fun _ -> Var elem) x *)
  subst_clause_set (fun x -> Func (elem,[])) x

(* let check_prop_satisfiability (elem: 'a) (x: 'a clauseset) : pmodel option =  *)
  (* x |> prop_abstraction elem |> to_pcnf |> call_sat_solver *)

(** Check propositional satisfiability of clauseset, and return propositional assignment, if any *)
let check_prop_satisfiability (elem: 'a) (x: 'a clauseset) : passignment option = 
  let numbering = x |> prop_abstraction elem |> prop_numbering in
  let pcnf = numbering |> numbering_to_pcnf in
  (* debug_endline pcnf; *)

  match call_sat_solver pcnf with
  | Some model -> (
    (* Array.iter (function true -> debug_string "T " | false -> debug_string "F ") model; debug_newline(); *)
    let aux = fun x -> let x' = abs(x)-1 in model.(x') = sign x in
    let assignments = List.map (List.map aux) (fst numbering) in
    Some assignments
  )
  | None -> None

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
    let r = List.map (fun {sign;lit} -> 
      {sign; lit = encode_atom lit}
    ) clause in
    table_var := Map.empty;
    num_var := -1;
    r
  ) x

let reencode_clauseset (x: int clauseset) : int clauseset =
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

  List.map (fun clause ->
    let r = List.map (fun {sign;lit} -> 
      {sign; lit = encode_atom lit}
    ) clause in
    table_var := Map.empty;
    num_var := -1;
    r
  ) x


(** Generate new instances of a clauseset, guided by an assignment *)
(* Look for unifiable literals 
 * Find them and apply to clauses where they appear
 * If not found return None
 *)
let inst_gen (formula: 'a clauseset) (assignments: passignment) : 'a clauseset option =
  (* (
    List.iter (fun x ->
      List.iter (
        function true -> debug_string "T " | false -> debug_string "F "
      ) x;
      debug_newline()
    ) assignments
  ); *)

  (** Return lazylist of potentially unifiable literals *)
  let pairs (l: 'a clauseset) : ('a literal * int * 'a literal * int) LazyList.t =
    let ret = ref LazyList.nil in

    let selecteds : int list = 
      (* List.map (List.find (fun {sign;lit} -> model.(lit-1) = sign)) l *)
      (* List.map (List.index_of true %> Option.get) assignments *)
      List.map (List.filteri_map (fun i elem -> if elem then Some i else None) %> List.shuffle %> List.hd) assignments
    in

    (* DEBUG *)
    debug_endline "Iteration";
    List.iter (fun x -> debug_int x; debug_newline()) selecteds;
    debug_newline();
    debug_endline "Finding unifiables...";

    List.iter2i (fun i clause_a ii ->
      List.iter2i (fun j clause_b jj ->
        (*ret := LazyList.cons (List.at clause_a ii, i, List.at clause_b jj, j) !ret*)  (*REEEEEEEEEEE*)
        ret := LazyList.cons (List.at clause_a ii, i, List.at clause_b jj, j+i+1) !ret
      ) (List.drop (i+1) l) (List.drop (i+1) selecteds)
    ) l selecteds;
    !ret
  in

  (* let rename = fun x -> Var (x^"'") in
  let dename = fun x -> Var (if String.ends_with x "'" then String.rchop x else x) in *)

  (* let dename = fun x -> Var (if x mod 2 = 0 then x-1 else x) in *)  (* REEEEEEE *)
  let rename = fun x -> Var (x-1) in
  let dename = fun x -> Var (if x mod 2 = 0 then x+1 else x) in

  (* Tries to unify a and b *)
  let try_unify (a: 'a literal) (b: 'a literal) =
    let b = subst_literal rename b in

    debug_endline (string_of_int_literal a);
    debug_endline (string_of_int_literal b);
    debug_endline "";

    let {sign=asign; lit=Pred (aname, aargs)} = a in
    let {sign=bsign; lit=Pred (bname, bargs)} = b in

    (* Potentially unifiable if: same name, opposite sign *)
    if aname == bname && asign <> bsign then
      (* And if unification succeeds *)
      try
        let subst = mgu_list (List.combine aargs bargs) in
        Some subst
      with
      | Failure _ -> None
    else
      None
  in

  (** New clauses from clauses a and b and substitution subst *)
  let new_clauses (a: 'a clause) (b: 'a clause) subst : 'a clauseset = 
    let clause_a = subst_clause subst (a) in
    (* let clause_b = subst_clause subst (subst_clause rename @@ a) in  (* REEEEEE *) *)
    let clause_b = subst_clause (rename %> (fun (Var x) -> subst x)) b in

    (* let clause_a = subst_clause dename clause_a in
    let clause_b = subst_clause dename clause_b in *)

    reencode_clauseset (if clause_a = clause_b then [clause_a] else [clause_a; clause_b])
  in

  (** Filters clauses that are redundant in l *)
  let remove_redundant (c: 'a clauseset) (l: 'a clauseset) =
    debug_endline "testing";
    List.filter (fun x ->
      debug_endline @@ string_of_int_clause x;
      if List.mem x l then
        (debug_endline "exists"; false)
      else
        (debug_endline "new"; true)
    ) c
  in

  try
    let foo = 
      pairs formula
      |> LazyList.to_list |> List.shuffle |> LazyList.of_list (* Randomize *)
      |> LazyList.map (fun (a,i,b,j) -> 
        debug_int i; debug_string "/"; debug_int j; debug_newline();
        let s = try_unify a b in match s with Some subst -> Some (i,j,subst) | None -> None
      )
      (* |> LazyList.map (function Some (i,j,s) -> let n = new_clauses (List.at formula i) (List.at formula j) s in let n' = remove_redundant n formula in if List.is_empty n' then None else Some n' | None -> None) *)
      |> LazyList.map ((flip Option.bind) (fun (i,j,s) ->
        let a = List.at formula i in
        let b = List.at formula j in
        let n = new_clauses a b s in 
        let n = remove_redundant n formula in 
        if List.is_empty n then None else Some n 
      ))
      |> LazyList.find (function Some _ -> true | None -> false) 
    in
    foo
    
  with
  | Not_found -> None



(* Main loop *)

(** Main loop:
  *   - Check satisfiability
  *   - If UNSAT, we are done
  *   - If SAT, use the model to guide generation of clauses, add them to the set, and repeat
  *)
let main_loop (l: 'a clauseset) : bool = 
  let designated : 'a = 
    list_functions_clauseset l
    (* |> List.filter (fun x -> snd x = 0)
    |> List.shuffle
    |> List.hd |> fst *)
    |> List.group compare
    (* |> List.map List.length *)
    |> List.min_max ~cmp:(fun x y -> compare (List.length x) (List.length y)) 
    |> snd |> List.hd |> fst
  in
  print_int designated; print_newline();

  let rec loop it l =
    print_string @@ "\rIt: " ^ string_of_int it; flush stdout;

    debug_endline "Current clauses:";
    debug_endline @@ string_of_int_clauseset l;
    debug_endline "End.\n";

    match check_prop_satisfiability designated l with
    | Some assignments -> (
      let new_clauses = inst_gen l assignments in
      match new_clauses with
      | Some x -> (
        debug_endline "More clauses added:"; 
        debug_endline @@ string_of_int_clauseset x;
        debug_endline "---\n";
        loop (succ it) (l @ x)
      )
      | None -> (
        debug_endline "None unifiable: saturated."; 
        true
      )
    )
    | None -> (
      debug_endline "Prop solver returned unsat."; 
      false
    )
  in
  print_newline();
  loop 0 l





let test_cnf() =
  let input = IO.read_all stdin in

  print_endline @@ bold "Original formula:";
  let test_formula = Parser.parse_cnf input in
  print_endline @@ string_of_clauseset test_formula;
  print_newline();
  
  print_endline @@ bold "Encoded formula:";
  let encoded_formula = encode_clauseset test_formula in
  print_endline @@ string_of_int_clauseset encoded_formula;
  print_newline();

  print_endline @@ bold "Propositional abstraction:";
  let designated = 
    list_functions_clauseset encoded_formula
    |> List.filter (fun x -> snd x = 0)
    |> List.shuffle
    |> List.hd |> fst
  in
  print_endline @@ string_of_int designated;
  (* let prop_formula = prop_abstraction 0 encoded_formula in *)
  let prop_formula = prop_abstraction designated encoded_formula in
  print_endline @@ string_of_int_clauseset @@ prop_formula;
  print_newline();
  
  print_endline @@ bold "pcnf text:";
  print_string @@ to_pcnf prop_formula;
  print_newline();
  
  print_endline @@ bold "Prop satisfiability of above:";
  (* let sat = check_prop_satisfiability 0 prop_formula in *)
  (* let sat = check_prop_satisfiability 0 encoded_formula in *)
  let sat = check_prop_satisfiability designated encoded_formula in
  print_endline @@ (match sat with Some _ -> "SAT" | None -> "UNSAT");
  print_newline();

  (* print_endline "Starting instance generation";
  let new_instances = inst_gen test_formula in
  print_endline "Done";

  begin match new_instances with
  | Some x -> 
    print_endline @@ string_of_clauseset x
  | None ->
    print_endline "None found"
  end; (* SEM O END PENSA QUE O RESTO TÁ DEBAIXO DO NONE *)
  print_newline(); *)

  let sat = main_loop encoded_formula in
  print_endline @@ if sat then "FOL SAT" else "FOL UNSAT";

  ()



let test_formula() =
  let input = IO.read_all stdin in

  print_endline @@ bold "Input:";
  print_endline input;

  print_endline @@ bold "Original formula:";
  let test_formula = Parser.parse_file input in
  print_endline @@ string_of_formula test_formula;
  print_newline();
  
  print_endline @@ bold "Skolemized:";
  (* let skolem_formula = Clausification.skolemize (Not test_formula) in *)
  let skolem_formula = Clausification.skolemize (test_formula) in
  print_endline @@ string_of_formula skolem_formula;
  print_newline();
  
  print_endline @@ bold "CNF:";
  let cnf_formula = Clausification.clausify skolem_formula in
  print_endline @@ string_of_clauseset cnf_formula;
  print_newline();
  
  print_endline @@ bold "Equality axioms:";
  let eq_axioms = Equality.axioms_string cnf_formula in
  print_endline @@ string_of_clauseset eq_axioms;
  print_newline();
  
  (* print_endline @@ bold "Optimized CNF:";
  let cnf_formula = Clausification.clausify_opt test_formula in
  print_endline @@ string_of_clauseset cnf_formula;
  print_newline(); *)
  
  let sat = main_loop @@ encode_clauseset (cnf_formula @ eq_axioms) in
  print_endline @@ if sat then "FOL SAT" else "FOL UNSAT";

  ()



let () = test_formula()
