open Batteries

open Types
open Util

open Debug



type clause_i = {
  l: int clause;
}

type clauseset_i = {
  l: int clauseset;
}

module Trie = Trie.Literal
type 'a trie = ('a literal * 'a clause) Trie.t

type passive = {
  l: int clause list;
}

type active = {
  l: (int literal * int clause) list;
}

type instgen_state = {
  mutable formula: clauseset_i;
  mutable trie: int trie;
  mutable passive: passive;
  mutable active: active;
}



(* --- *)

(** Returns true if saturated, otherwise false *)
let rec instgen (s: instgen_state) (assignments: Propositional.assignment) : bool =
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

  if dbg_flag then (
    debug_newline();

    debug_endline "Formula:";
    s.formula.l |> List.iter (fun x -> debug_endline @@ "  " ^ string_of_int_clause x);
    debug_endline "Active:";
    s.active.l |> List.iter (fun (l,x) -> debug_endline @@ "  " ^ string_of_int_clause x ^ " [" ^ string_of_int_literal l ^ "]");
    debug_endline "Passive:";
    s.passive.l |> List.iter (fun x -> debug_endline @@ "  " ^ string_of_int_clause x);
  );

  (** Return map assigning clauses to selected literals *)
  let selecteds_map : (int clause, int literal) Map.t =
    let ret = ref Map.empty in

    let rec loop clause' assignment' = 
      match clause', assignment' with
      | lit::xs, true::ys -> lit
      | lit::xs, false::ys -> loop xs ys
      | [],_ | _,[] -> failwith "selecteds_map:loop: should not happen"
    in

    List.iter2 (fun clause assignment ->
      ret := Map.add clause (loop clause assignment) !ret
    ) s.formula.l assignments;
    !ret
  in

  let rename = fun x -> Var (x-1) in
  let dename = fun x -> Var (if x mod 2 = 0 then x+1 else x) in

  (* Tries to unify a and b *)
  let try_unify_lits (a: 'a literal) (b: 'a literal) =
    let b = subst_literal rename b in

    if dbg_flag then begin
    debug_endline (string_of_int_literal a);
    debug_endline (string_of_int_literal b);
    debug_endline "";
    end;

    let {sign=asign; atom=Pred(aname, aargs)} = a in
    let {sign=bsign; atom=Pred(bname, bargs)} = b in

    (* Potentially unifiable if: same name, opposite sign *)
    if aname = bname && asign <> bsign then  (* WAS== *)
      (* And if unification succeeds *)
      try
        let subst = Unification.mgu_list (List.combine aargs bargs) in
        Some subst
      with
      | Failure _ -> None
    else
      None
  in

  let try_unify_atoms a b =
    let b = subst_atom rename b in
    let Pred(_, aargs) = a in
    let Pred(_, bargs) = b in    
    try
      let subst = Unification.mgu_list (List.combine aargs bargs) in
      Some subst
    with
    | Failure _ -> None
  in

  let try_unify_atoms_map a b =
    let b = subst_atom rename b in
    let Pred(_, aargs) = a in
    let Pred(_, bargs) = b in    
    try
      let subst = Unification.mgu_list_map (List.combine aargs bargs) in
      Some subst
    with
    | Failure _ -> None
  in

  (** New clauses from clauses a and b and substitution subst *)
  (* make_new_clauses (a: 'a clause) (b: 'a clause) subst : 'a clauseset = 
    let clause_a = subst_clause subst (a) in
    let clause_b = subst_clause (rename %> (fun (Var x) -> subst x)) b in

    (* let clause_a = subst_clause dename clause_a in
    let clause_b = subst_clause dename clause_b in *)
    Util.reencode_clauseset (if clause_a = clause_b then [clause_a] else [clause_a; clause_b])
  in *)
  let make_new_clauses (a: 'a clause) (b: 'a clause) subst (set: 'a clauseset) : 'a clauseset = 
    let subst_func = Unification.map_to_func subst in

    let vars_relevant = List.of_enum @@ Enum.filter_map (function (_, Var _) -> None | (x, Func _) -> Some x) (Map.enum subst) in
    let proper_instantiator cls relevant =
      list_vars_clause cls |> Enum.exists (fun x -> List.mem x relevant)
    in

    let a' = subst_clause subst_func a |> Util.reencode_clause in
    let proper_a = proper_instantiator a vars_relevant in
    let existing_a = List.mem a' set in
    if existing_a && proper_a then (
      if dbg_flag then (debug_endline "Redundant inference");
      []
    ) else (
      let b' = subst_clause (rename %> (fun (Var x) -> subst_func x)) b |> Util.reencode_clause in
      let proper_b = proper_instantiator b vars_relevant in
      let existing_b = List.mem b' set in
      if existing_b && proper_b then (
        if dbg_flag then (debug_endline "Redundant inference");
        []
      ) else (
        match existing_a, existing_b with
        | true , true  -> []
        | false, true  -> [a']
        | true , false -> [b']
        | false, false -> if a' = b' then [a'] else [a';b']
      )
    )
  in

  (** Filters clauses in c that are redundant in l *)
  (* Currently just membership testing *)
  let remove_redundant (c: 'a clauseset) (l: 'a clauseset) =
    if dbg_flag then begin
    debug_endline "testing";
    end;
    List.filter (fun x ->
      if dbg_flag then (
        debug_endline @@ string_of_int_clause x;
        if List.mem x l then
          (debug_endline "exists"; false)
        else
          (debug_endline "new"; true)
      ) else (
        not $ List.mem x l
      )
    ) c
  in

  if dbg_flag then begin
    (* debug_endline "Selecteds:";
    List.iter (fun (lit,clause) -> debug_endline @@ string_of_int_literal lit ^ " /in/ " ^ string_of_int_clause clause) selecteds;
    debug_endline "Selecteds_set:";
    Set.iter (fun (atom,clause) -> debug_endline @@ string_of_int_atom atom ^ " /in/ " ^ string_of_int_clause clause) selecteds_set;
    debug_newline(); *)
  end;

  (* Given clause algorithm:
     - Grab first clause from passive
     - Perform all inferences with all clauses in active
     - If in any inference it is found that selection has changed, put that into passive
     - If any inferences were made, good, put 
     - Else, put anyways but do another inst-gen loop
     - If passive is empty, it is saturated
   *)

  (** Return (given_clause, rest_of_passive) *)
  (* Currently just selects front clause *)
  let select_given_clause l : int clause * int clause list = 
    match l with
    | x::xs -> (x, xs)
    | [] -> invalid_arg "select_given_clause: nonempty list"
  in

  (* If passive is empty, it is saturated *)
  if List.is_empty s.passive.l then (
    true
  ) 

  else (
    let given_clause, rest = select_given_clause s.passive.l in
    s.passive <- {l = rest};
    let given_lit = Map.find given_clause selecteds_map in
    if dbg_flag then (
      debug_endline @@ "Given clause: " ^ string_of_int_clause given_clause ^ " [" ^ string_of_int_literal given_lit ^ "]"
    );

    let candidates = Trie.unifiable s.trie given_lit in
    let new_clauses = 
      candidates
      |> List.filter_map (fun (candidate_lit, candidate_clause) ->
        if dbg_flag then (
          debug_string @@ Printf.sprintf "  Candidate: %s [%s] " (string_of_int_clause candidate_clause) (string_of_int_literal candidate_lit)
        );

        (* Check if in active *)
        match List.find_opt (fun (_,c) -> c = candidate_clause) s.active.l with
        | None -> (
          if dbg_flag then (debug_endline "NOT ACTIVE");
          None
        )

        | Some ((lit', clause') as foo') -> (
          let selection_lit = Map.find candidate_clause selecteds_map in

          (* Unselected *)
          if selection_lit <> candidate_lit then (
            if dbg_flag then (debug_endline "NOT SELECTED");
            None
          )

          (* Selection changed *)
          else if selection_lit <> lit' then (
            if dbg_flag then (debug_endline "SEL CHANGED");
            (* Move clause to passive *)
            s.active <- {l = List.remove s.active.l (foo')};
            s.passive <- {l = clause' :: s.passive.l};
            None
          )

          (* Selection ok, do inference *)
          else (
            match try_unify_atoms_map given_lit.atom candidate_lit.atom with
            | Some subst -> (
              if dbg_flag then (debug_newline());
              let n = make_new_clauses given_clause candidate_clause subst s.formula.l in
              if dbg_flag then (debug_endline "ACCEPTED");
              Some n        
            )
            | None -> (
              (* debug_printf "%s %s" (string_of_int_atom given_lit.atom) (string_of_int_atom candidate_lit.atom);
              failwith "instgen: nonunifiable (should not happen)" *)
              if dbg_flag then (debug_endline "NONUNIFIABLE (should not happen)");
              None
            )
          )
        )

      )
      |> List.concat
    in

    s.active <- {l = (given_lit, given_clause) :: s.active.l};
    match new_clauses with
    | [] -> (
      if dbg_flag then (
        debug_endline "No inferences with this given clause, trying more."
      );
      instgen s assignments
    )
    | new_clauses -> (
      if dbg_flag then (
        debug_endline "New clauses:";
        List.iter (fun x -> debug_endline @@ string_of_int_clause x) new_clauses;
        debug_endline "End.";
      );

      let new_clauses = List.sort_unique compare new_clauses in

      if dbg_flag then (
        debug_endline "New clauses:";
        List.iter (fun x -> debug_endline @@ string_of_int_clause x) new_clauses;
        debug_endline "End.";
      );

      s.formula <- {l = s.formula.l @ new_clauses};
      s.passive <- {l = s.passive.l @ new_clauses};
      new_clauses |> List.iter (fun cls ->
        cls |> List.iter (fun lit ->
          s.trie <- Trie.insert s.trie lit (lit,cls)
        )
      );
      false
    )
  )



(* Main loop *)

(** Main loop:
  *   - Check satisfiability
  *   - If UNSAT, we are done
  *   - If SAT, use the model to guide generation of clauses, add them to the set, and repeat
  *)
let main_loop (l: int clauseset) : bool = 
  let designated : int = 
    list_functions_clauseset l
    |> List.filter (function (_,0) -> true | _ -> false)
    |> List.group compare
    |> List.min_max ~cmp:(fun x y -> compare (List.length x) (List.length y)) |> snd 
    |> List.hd |> fst
  in
  if dbg_flag then (
    debug_printf "Designated: %d" designated
  );

  (* Initial insertion of terms into trie *)
  let trie : int trie = Trie.create() in
  let add_clauseset_to_trie (trie: int trie) (l: int clauseset) : int trie = 
    let trie = ref trie in
    List.iter (fun clause ->
      List.iter (fun lit -> 
        if dbg_flag then (debug_endline @@ "Adding " ^ string_of_int_literal lit);
        trie := Trie.insert !trie lit (lit,clause)
      ) clause
    ) l;
    !trie
  in
  let trie = add_clauseset_to_trie trie l in
  let state = {
    formula = {l = l};
    trie = trie;
    active = {l = []};
    passive = {l = l};
  }
  in

  let rec loop it state =
    if it = 500 then false else (

    print_string @@ "\rIt: " ^ string_of_int it; flush stdout;

    if dbg_flag then (
      debug_endline @@ "It: " ^ string_of_int it;
    );

    match Propositional.satisfiable ~elem:designated (state.formula.l) with
    | Some assignments -> (
      let saturated = instgen state assignments in
      if not saturated then (
        loop (succ it) (state)
      ) else (
        if dbg_flag then (
          debug_endline "None unifiable: saturated.";
        );
        true
      )
    )
    | None -> (
      if dbg_flag then (
        debug_endline "Prop solver returned unsat.";
      );
      false
    )

    )
  in

  print_newline();
  loop 0 state
