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

(** Generate new instances of a clauseset, guided by an assignment *)
(* Look for unifiable literals 
 * Find them and apply to clauses where they appear
 * If not found return None
 *)
(* Returns true if saturated, otherwise false *)
let rec instgen (s: instgen_state) (assignments: passignment) : bool =
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

  (** Return lazylist of potentially unifiable literals *)
  (* let pairs (l: 'a clauseset) : ('a literal * int * 'a literal * int) Seq.t =
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
  in *)

  (** Return list of selected literals *)
  (* let selecteds : ('a literal * 'a clause) List.t =
    let ret = ref [] in

    let selecteds' : int list = 
      if not dbg_flag then (
        List.map (List.index_of true %> Option.get) assignments
      ) 

      else (
        debug_endline "Iteration";
        List.map (fun c -> 
          List.index_of true c |> Option.get
          |> tap (fun x -> debug_int x; debug_newline())
        ) assignments
        |> tap (const @@ debug_endline "Finding unifiables...")
      )
    in

    (* debug_endline "Iteration";
    List.iter (fun x -> debug_int x; debug_newline()) selecteds';
    debug_newline();
    debug_endline "Finding unifiables...";
    end; *)

    List.iter2 (fun clause ii ->
      ret := (List.at clause ii, clause) :: !ret
    ) formula selecteds';
    !ret
  in *)

  (** Return list of selected literals *)
  let selecteds_map : (int clause, int literal) Map.t =
    let ret = ref Map.empty in

    (* let selecteds' : int list = 
      if not dbg_flag then (
        List.map (List.index_of true %> Option.get) assignments
      ) else (
        debug_endline "Iteration";
        List.map (fun c -> 
          List.index_of true c |> Option.get
          |> tap (fun x -> debug_int x; debug_newline())
        ) assignments
        |> tap (fun _ -> debug_endline "Finding unifiables...")
      )
    in *)

    (* debug_endline "Iteration";
    List.iter (fun x -> debug_int x; debug_newline()) selecteds';
    debug_newline();
    debug_endline "Finding unifiables...";
    end; *)

    List.iter2 (fun clause assignment ->
      (* ret := Map.add clause (List.at clause ii) !ret *)
      let rec loop clause' assignment' = 
        match clause', assignment' with
        | lit::xs, true::ys -> lit
        | lit::xs, false::ys -> loop xs ys
        | [],_ | _,[] -> failwith "selecteds_map:loop: should not happen"
      in
      ret := Map.add clause (loop clause assignment) !ret
    ) s.formula.l assignments;
    !ret
  in

  (* let selecteds_set : ('a atom * 'a clause) Set.t = 
    selecteds |> List.enum |> Enum.map (fun ({lit;sign},clause) -> (lit,clause)) |> Set.of_enum
  in *)

  let rename = fun x -> Var (x-1) in
  let dename = fun x -> Var (if x mod 2 = 0 then x+1 else x) in

  (* Tries to unify a and b *)
  (* let try_unify_lits (a: 'a literal) (b: 'a literal) =
    let b = subst_literal rename b in

    if dbg_flag then begin
    debug_endline (string_of_int_literal a);
    debug_endline (string_of_int_literal b);
    debug_endline "";
    end;

    let {sign=asign; lit=Pred(aname, aargs)} = a in
    let {sign=bsign; lit=Pred(bname, bargs)} = b in

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
  in *)

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

  (* let is_inference_redundant (premise: int clause) (conclusion: int clause) subst (set: int clauseset) =
    if dbg_flag then (
      debug_endline @@ "    Testing " ^ string_of_int_clause conclusion;
      debug_endline @@ "    With subst: " ^ string_of_int_subst subst;
    );
    let proper_instantiator subst cls = 
      (* Enum.filter_map (function (_, Var _) -> false | _ -> true) (Map.values subst) *)
      let vars_relevant = List.of_enum @@ Enum.filter_map (function (_, Var _) -> None | (x, Func _) -> Some x) (Map.enum subst) in
      let vars_cls = list_vars_clause cls in
      vars_cls |> Enum.exists (fun x -> List.mem x vars_relevant)
    in
    proper_instantiator subst premise && List.mem conclusion set
  in *)

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
        | false, true  -> [a']  (* REEE *)
        | true , false -> [b']  (* REEE *)
        | false, false -> if a' = b' then [a'] else [a';b']
      )
    )
  in

  (** Filters clauses in c that are redundant in l *)
  (* let remove_redundant (c: 'a clauseset) (l: 'a clauseset) =
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
  in *)

  (** Tells you if any clause in c is redundant in l *)
  (* let any_is_redundant c l =
    List.exists (fun x -> List.mem x l) c
  in *)


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

  let select_given_clause l : int clause * int clause list = 
    (* List.hd l *)
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
    if dbg_flag then (debug_endline @@ "Given clause: " ^ string_of_int_clause given_clause ^ " [" ^ string_of_int_literal given_lit ^ "]");

    let candidates = Trie.unifiable s.trie given_lit in
    let new_clauses = 
      candidates
      (* |> List.filter_map (fun ((candidate_lit, candidate_clause) as foo) -> *)
      |> List.filter_map (fun (candidate_lit, candidate_clause) ->
        if dbg_flag then (
          debug_string @@ Printf.sprintf "  Candidate: %s [%s] " (string_of_int_clause candidate_clause) (string_of_int_literal candidate_lit)
        );

        (* Check if in active *)
        (* match List.find (foo) s.active.l with *)
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
            (* Move clause to passive *)
            if dbg_flag then (debug_endline "SEL CHANGED");
            s.active <- {l = List.remove s.active.l (foo')};
            s.passive <- {l = clause' :: s.passive.l};
            None
          )
          (* Selection ok, do inference *)
          else (
            (* let subst = try_unify_atoms given_lit.lit candidate_lit.lit |> Option.get in *)
            match try_unify_atoms_map given_lit.lit candidate_lit.lit with
            | Some subst -> (
              if dbg_flag then (debug_newline());
              (* let n = make_new_clauses given_clause candidate_clause (Unification.map_to_func subst) in *)
              let n = make_new_clauses given_clause candidate_clause subst s.formula.l in
              (* if any_is_redundant n s.formula.l then ( *)  
              (* if List.exists2 (fun x y -> is_inference_redundant x y subst s.formula.l) n [given_clause; candidate_clause] then ( *)
              (* if List.exists2 (fun x y -> is_inference_redundant x y subst s.formula.l) [given_clause; candidate_clause] n then (
                if dbg_flag then (debug_endline "SOME REDUNDANT CONCLUSION");
                None
              ) else *) (
                if dbg_flag then (debug_endline "ACCEPTED");
                Some n
              )
              (* let n = remove_redundant n s.formula.l in
              if dbg_flag then (debug_endline "ACCEPTED");
              Some n    *)           
            )
            | None -> (
              if dbg_flag then (debug_endline "NONUNIFIABLE");
              None
            )
          )
        )

      )
      |> List.concat
    in
    s.active <- {l = (given_lit, given_clause) :: s.active.l};
    match new_clauses with
    | [] -> instgen s assignments
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
          s.trie <- Trie.insert s.trie lit (lit,cls) (* Move / nah its ok *)
        )
      );
      false
    )
  )



  (* begin try
    let open Option.Infix in
    (* Grab list of selecteds *)
    selecteds (* |> List.rev *) |> List.shuffle
    (* For each clause, grab the selected literal *)
    |> List.find_map (fun (lit,clause) ->
      if dbg_flag then begin
        debug_endline @@ "> " ^ string_of_int_literal lit ^ " /in/ " ^ string_of_int_clause clause
      end;
      (* Find unifiable candidates *)
      let (candidates: ('a literal * 'a clause) list) = Trie.unifiable trie lit in
      if dbg_flag then (
        debug_endline @@ Int.to_string (List.length candidates) ^ " candidates:";
        List.iter (debug_endline % string_of_int_literal % fst) candidates;
        debug_endline "End.";
      );
      (* Find candidate that has: different clause; selected; syntactic unifiability*)
      begin try
        candidates
        |> List.find_map (fun (lit',clause') -> 
          begin 
            if dbg_flag then (debug_endline @@ ">   " ^ string_of_int_literal lit' ^ " /in/ " ^ string_of_int_clause clause');
            if clause == clause' || clause = clause' then (
              if dbg_flag then (debug_endline "[same clause]");
              None
            (* ) else if not (Set.mem (lit',clause') selecteds_set) then ( *)
            ) else if not (List.exists (fun (lit'',clause'') -> lit'' == lit' && clause'' == clause') selecteds) then (
              if dbg_flag then (debug_endline "[not selected]");
              None            
            ) else (
              let subst = try_unify_lits lit lit' in
              (* debug_endline "fooo"; *)
              match subst with
              | Some x -> (
                if dbg_flag then (debug_endline "gtg");
                Some (clause, clause', x)
              )
              | None -> (
                if dbg_flag then (debug_endline "[not unifiable]");
                None
              )
            ) 
          end

          (* Build new clauses and check if redundant *)
          >>= (fun (a,b,subst) ->
            (* if dbg_flag then (debug_endline @@ "foooooo"); *)
            let n = make_new_clauses a b subst in (* Build new clauses *)
            if dbg_flag then (debug_endline @@ "New clauses: " ^ string_of_int_clauseset n);
            let n = remove_redundant n formula in (* Remove redundant clauses *)
            if List.is_empty n then None else Some n (* Unless all clauses were redundant, return success *)
          )
        )
        |> Option.some
        (* |> tap (fun _ -> debug_endline "foo") *)
      with
      | Not_found -> (if dbg_flag then (debug_endline "[[not_found]]"); None)
      end
    )
  |> Option.some
  with Not_found -> None
  end *)



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

  (* Initial insertion of terms into trie *)
  let trie : int trie = Trie.create() in
  let add_clauseset_to_trie (trie: 'a trie) (l: 'a clauseset) : 'a trie = 
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
    print_string @@ "\rIt: " ^ string_of_int it; flush stdout;

    if dbg_flag then begin
    debug_endline @@ "It: " ^ string_of_int it;
    (* debug_endline "Current clauses:";
    debug_endline @@ string_of_int_clauseset l;
    debug_endline "End.\n"; *)
    end;

    (* match check_prop_satisfiability designated l with *)  (* OOPS *)
    match check_prop_satisfiability designated (state.formula.l) with
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
  in

  print_newline();
  loop 0 state
