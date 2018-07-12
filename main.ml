open Batteries

open Types
open Unification
open Util

let prop_abstraction (elem: 'a) (x: 'a clauseset) = 
  subst_clause_set (fun x -> Var elem) x

let check_prop_satisfiability (elem: 'a) (x: 'a clauseset) : pmodel option = 
  x |> prop_abstraction elem |> to_pcnf |> call_sat_solver

let encode_clauseset (x: string clauseset) : int clauseset =
  let table = ref @@ Map.empty in
  let num = ref 1 in
  let table_var = ref @@ Map.empty in
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

let inst_gen (x: 'a clauseset) : 'a clauseset option =
  (* Look for unifiable literals 
   * Find them and apply to clauses where they appear
   * If not found return None
   *)

  (* Terrible performance *)
  (* type 'a pair = 
    { n1: int
    ; n2: int
    ; lit1: 'a literal
    ; lit2: 'a literal
    } *)
  let pairs (l: 'a clauseset) : ('a literal * int * 'a literal * int) LazyList.t =
    let ret = ref LazyList.nil in

    let n = List.length l - 1 in
    (* Pairs of clauses *)
    for i = 0 to n do
      let clause_a = List.at l i in
      for j = i+1 to n do
        let clause_b = List.at l j in
        (* In these clauses, pairs of elements *)
        let na = List.length clause_a - 1 in
        let nb = List.length clause_b - 1 in
        for ii = 0 to na do
          for jj = 0 to nb do
            ret := LazyList.cons (List.at clause_a ii, i, List.at clause_b jj, j) !ret
          done
        done

      done
    done;
    !ret

    (* let rec loop_2nd_clause l ls =
      match ls with
      | [] -> None
      | x::xs ->


    let rec loop_1st_clause l = 
      match l with
      | [] -> None
      | x::xs ->
        loop_2nd clause x xs
    in
    loop_1st_clause x *)

(*   let attempt a b =
    try
      let subst = mgu (a,b) in

    with
    | Failure _ -> None *)

  in

  let try_unify (a,i,b,j) =
    (* let b = subst_literal (fun x -> Var (x^"'")) b in *)

    let {sign=asign; lit=Pred (aname, aargs)} = a in
    let {sign=bsign; lit=Pred (bname, bargs)} = b in

    print_endline @@ string_of_literal a;
    print_endline @@ string_of_literal b;
    print_newline ();

    if asign == bsign || aname <> bname then
      None
    else
      try
        (* let bargs' = List.map (subst_term (fun x -> Var (x^"'"))) bargs in *)
        let subst = mgu_list (List.combine aargs bargs) in
        (* let subst = fun x -> 
          if String.ends_with "'" x then 
            subst (String.rchop x)
          else 
            subst x
        let subst = fun x ->
          let Var y = subst x
        in *)
        (* let subst' = (fun x -> if String.ends_with "'" x then subst (String.rchop x) else subst x) in *)
        Some (i,j,subst)
        (* Some (i,j,subst,subst) *)
      with
      | Failure _ -> None
  in

  let rename = fun x -> Var (x^"'") in
  let dename = fun x -> Var (if String.ends_with x "'" then String.rchop x else x) in

  (* let pair = LazyList.find (function Some _ -> true | None -> False) in *)
  try
    (* let i,j,s = LazyList.find_map try_unify (pairs x) in *)
    (* let Some (i,j,s) = LazyList.find (function Some _ -> true | None -> false) @@ LazyList.map try_unify (pairs x) in *)
    let foo = 
      pairs x
      |> LazyList.map (fun (a,i,b,j) -> (a,i,subst_literal rename b,j))
      |> LazyList.map try_unify
      |> LazyList.find (function Some _ -> true | None -> false) 
    in
    let Some (i,j,s) = foo in
    (* let Some (i,j,sa,sb) = foo in *)
    (* Some [subst_clause s (List.at x i); subst_clause s (List.at x j)] *)
    (* Some [subst_clause sa (List.at x i); subst_clause sb (List.at x j)] *)
    
    let clause_a = subst_clause s (List.at x i) in
    let clause_b = subst_clause s (subst_clause rename @@ List.at x j) in

    let clause_a = subst_clause dename clause_a in
    let clause_b = subst_clause dename clause_b in

    Some [clause_a; clause_b]

  with
  | Not_found -> None



let rec main_loop (l: 'a clauseset) : bool = 
  match check_prop_satisfiability "X" l with
  | Some _ ->
    let new_clauses = inst_gen l in
    (* case new_clauses of *)
    match new_clauses with
    | Some x -> (print_endline "new"; main_loop (l @ x))
    | None -> true
  | None ->
    false

let test () =
  (* let test_formula = 
    (* [ [{sign=true; lit=}]
    ;
    ] *)
    Parser.parse "~g(f(x),y)asdas" in
  (* print_string @@ string_of_atom test_formula.lit *)
  (* print_string @@ string_of_literal test_formula *)
  print_string @@ string_of_clauseset test_formula *)

  let input = IO.read_all stdin in
  let test_formula = Parser.parse input in
  print_endline @@ string_of_clauseset test_formula;
  print_newline ();
  
  let encoded_formula = encode_clauseset test_formula in
  print_endline @@ string_of_int_clauseset encoded_formula;
  print_newline ();

  let prop_formula = prop_abstraction 0 encoded_formula in
  print_endline @@ string_of_int_clauseset @@ prop_formula;
  print_newline ();
  
  print_string @@ to_pcnf prop_formula;
  print_newline ();
  
  (* let sat = check_prop_satisfiability 0 prop_formula in *)
  let sat = check_prop_satisfiability 0 encoded_formula in
  print_endline @@ (match sat with Some _ -> "SAT" | None -> "UNSAT");

  (*let pairs = inst_gen test_formula in
  (* LazyList.iter (fun (x,y) -> print_endline @@ string_of_int_literal x ^ " / " ^ string_of_int_literal y) pairs;  *)
  LazyList.iter (fun (x,y) -> print_endline @@ string_of_literal x ^ " / " ^ string_of_literal y) pairs;*)

  print_endline "Starting instance generation";
  let new_instances = inst_gen test_formula in
  print_endline "Done";

  begin match new_instances with
  | Some x -> 
    print_endline @@ string_of_clauseset x
  | None ->
    print_endline "None found"
  end; (* SEM O END PENSA QUE O RESTO TÁ DEBAIXO DO NONE *)
  print_newline ();

  let sat = main_loop test_formula in
  print_endline @@ if sat then "FOL SAT" else "FOL UNSAT";

  ()

let () = test()
