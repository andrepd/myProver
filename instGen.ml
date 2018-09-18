open Batteries

open Types
open Util

open Debug

(** Map variables to elem *)
let prop_abstraction (elem: 'a) (x: 'a clauseset) = 
  (* subst_clause_set (fun _ -> Var elem) x *)
  subst_clause_set (fun x -> Func (elem,[])) x

(** Check propositional satisfiability of clauseset, and return propositional assignment, if any *)
let check_prop_satisfiability (elem: 'a) (x: 'a clauseset) : passignment option = 
  let numbering = x |> prop_abstraction elem |> prop_numbering in
  let pcnf = numbering |> numbering_to_pcnf in
  (* debug_endline pcnf; *)

  match call_sat_solver pcnf with
  | Some model -> (
    (* Array.iter (function true -> debug_string "T " | false -> debug_string "F ") model; debug_newline(); *)
    let sign x = x > 0 in
    let aux = fun x -> let x' = abs(x)-1 in model.(x') = sign x in
    let assignments = List.map (List.map aux) (fst numbering) in
    Some assignments
  )
  | None -> None

(* --- *)

type 'a clause_i = {
  clause: 'a clause;
}

type 'a clauseset_i = {
  clauseset: 'a clauseset;
}

type 'a instgen_state = {
  formula: 'a clauseset_i
}

(* --- *)

(** Generate new instances of a clauseset, guided by an assignment *)
(* Look for unifiable literals 
 * Find them and apply to clauses where they appear
 * If not found return None
 *)
let instgen (formula: 'a clauseset) (assignments: passignment) : 'a clauseset option =
  (* (
    if dbg_flag then begin
    List.iter (fun x ->
      List.iter (
        function true -> debug_string "T " | false -> debug_string "F "
      ) x;
      debug_newline()
    ) assignments
    end;
  ); *)

  (** Return lazylist of potentially unifiable literals *)
  let pairs (l: 'a clauseset) : ('a literal * int * 'a literal * int) Seq.t =
    let ret = ref Seq.nil in

    let selecteds : int list = 
      (* List.map (List.find (fun {sign;lit} -> model.(lit-1) = sign)) l *)
      List.map (List.index_of true %> Option.get) assignments
      (* List.map (List.filteri_map (fun i elem -> if elem then Some i else None) %> List.shuffle %> List.hd) assignments *)
    in

    if dbg_flag then begin
    debug_endline "Iteration";
    List.iter (fun x -> debug_int x; debug_newline()) selecteds;
    debug_newline();
    debug_endline "Finding unifiables...";
    end;

    List.iter2i (fun i clause_a ii ->
      List.iter2i (fun j clause_b jj ->
        ret := Seq.cons (List.at clause_a ii, i, List.at clause_b jj, j+i+1) !ret
      ) (List.drop (i+1) l) (List.drop (i+1) selecteds)
    ) l selecteds;
    !ret
  in

  (* let rename = fun x -> Var (x^"'") in
  let dename = fun x -> Var (if String.ends_with x "'" then String.rchop x else x) in *)

  let rename = fun x -> Var (x-1) in
  let dename = fun x -> Var (if x mod 2 = 0 then x+1 else x) in

  (* Tries to unify a and b *)
  let try_unify (a: 'a literal) (b: 'a literal) =
    let b = subst_literal rename b in

    if dbg_flag then begin
    debug_endline (string_of_int_literal a);
    debug_endline (string_of_int_literal b);
    debug_endline "";
    end;

    let {sign=asign; lit=Pred(aname, aargs)} = a in
    let {sign=bsign; lit=Pred(bname, bargs)} = b in

    (* Potentially unifiable if: same name, opposite sign *)
    if aname == bname && asign <> bsign then
      (* And if unification succeeds *)
      try
        let subst = Unification.mgu_list (List.combine aargs bargs) in
        Some subst
      with
      | Failure _ -> None
    else
      None
  in

  (** New clauses from clauses a and b and substitution subst *)
  let make_new_clauses (a: 'a clause) (b: 'a clause) subst : 'a clauseset = 
    let clause_a = subst_clause subst (a) in
    let clause_b = subst_clause (rename %> (fun (Var x) -> subst x)) b in

    (* let clause_a = subst_clause dename clause_a in
    let clause_b = subst_clause dename clause_b in *)
    Util.reencode_clauseset (if clause_a = clause_b then [clause_a] else [clause_a; clause_b])
  in

  (** Filters clauses in c that are redundant in l *)
  let remove_redundant (c: 'a clauseset) (l: 'a clauseset) =
    if dbg_flag then begin
    debug_endline "testing";
    end;
    List.filter (fun x ->
      if dbg_flag then begin
      debug_endline @@ string_of_int_clause x;
      if List.mem x l then
        (debug_endline "exists"; false)
      else
        (debug_endline "new"; true)
      end else begin
      not $ List.mem x l
      end;
    ) c
  in

  let new_clauses = 
    let open Option.Infix in
    pairs formula
    (* |> Seq.to_list |> List.shuffle |> Seq.of_list (* Randomize *) *)
    |> Seq.map (
      fun (a,i,b,j) -> 
      if dbg_flag then begin
      debug_int i; debug_string "/"; debug_int j; debug_newline();
      end;
      let subst = try_unify a b in (* Try to unify *)
      begin match subst with Some subst -> Some (i,j,subst) | None -> None end (* If successful return clause indices and substitution *)
      >>= fun (i,j,subst) ->
      let a = List.at formula i in
      let b = List.at formula j in
      let n = make_new_clauses a b subst in (* Build new clauses *)
      let n = remove_redundant n formula in (* Remove redundant clauses *)
      if List.is_empty n then None else Some n (* Unless all clauses were redundant, return success *)
    )
    |> Seq.find Option.is_some 
  in
  (* Option.get new_clauses *)
  match new_clauses with 
  | Some x -> x
  | None -> None
    


(* Main loop *)

(** Main loop:
  *   - Check satisfiability
  *   - If UNSAT, we are done
  *   - If SAT, use the model to guide generation of clauses, add them to the set, and repeat
  *)
let main_loop (l: 'a clauseset) : bool = 
  let designated : 'a = 
    list_functions_clauseset l
    |> List.filter (function (_,0) -> true | _ -> false)
    |> List.group compare
    |> List.min_max ~cmp:(fun x y -> compare (List.length x) (List.length y)) |> snd 
    |> List.hd |> fst
  in
  if dbg_flag then begin
  debug_string "Designated: "; debug_int designated; debug_newline()
  end;

  let rec loop it l =
    print_string @@ "\rIt: " ^ string_of_int it; flush stdout;

    if dbg_flag then begin
    debug_endline "Current clauses:";
    debug_endline @@ string_of_int_clauseset l;
    debug_endline "End.\n";
    end;

    match check_prop_satisfiability designated l with
    | Some assignments -> (
      let new_clauses = instgen l assignments in
      match new_clauses with
      | Some x -> (
        if dbg_flag then begin
        debug_endline "More clauses added:"; 
        debug_endline @@ string_of_int_clauseset x;
        debug_endline "End.\n";
        end;
        loop (succ it) (l @ x)
      )
      | None -> (
        if dbg_flag then begin
        debug_endline "None unifiable: saturated."; 
        end;
        true
      )
    )
    | None -> (
      if dbg_flag then begin
      debug_endline "Prop solver returned unsat."; 
      end;
      false
    )
  in

  print_newline();
  loop 0 l
