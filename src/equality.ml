open Batteries

open Types
open Util

open Debug

let contig_vars n = 
  Char.range 'a'
  |> Enum.take n
  |> map (fun x -> Var (Char.escaped x))
  |> List.of_enum

let axioms' (preds: (string * int) list) (funcs: (string * int) list) : string clauseset =
  (* Equality axiom for a function *)
  let axiom_func ((name,arity): (string * int)) : string clause =
    let f_left n = {sign=false; atom=Pred ("=", [
      Var ("x"^string_of_int n);
      Var ("y"^string_of_int n)
    ])} in
    let f_right x n = Var (x ^ string_of_int n) in

    let left = List.init arity f_left in
    let right = {sign=true; atom=Pred ("=", [
      Func (name, List.init arity (f_right "x"));
      Func (name, List.init arity (f_right "y"));
    ])} in

    if dbg_flag then begin
    debug_endline name;
    debug_endline $ string_of_clause (right :: left)
    end;
    right :: left
  in

  (* Equality axiom for a predicate *)
  let axiom_pred ((name,arity): (string * int)) : string clause =
    let f_left n = {sign=false; atom=Pred ("=", [
      Var ("x"^string_of_int n);
      Var ("y"^string_of_int n)
    ])} in
    let f_right x n = Var (x ^ string_of_int n) in

    let left = List.init arity f_left in
    let right = [
      {sign=false; atom=Pred (name, List.init arity (f_right "x"))};
      {sign=true;  atom=Pred (name, List.init arity (f_right "y"))};
    ] in

    if dbg_flag then begin
    debug_endline name;
    debug_endline $ string_of_clause (right @ left)
    end;
    right @ left
  in

  (* Axioms of reflexivity and transitivity (symmetry is implied) *)
  let equivalence_axioms = 
    let reflexivity = 
      Atom (Pred ("=",[Var "x";Var "x"]))
    in
    let transitivity = 
      Imp (
        And (
          Atom (Pred ("=",[Var "x";Var "y"])), 
          Atom (Pred ("=",[Var "x";Var "z"]))
        ),
        Atom (Pred ("=",[Var "y";Var "z"]))  
      )
    in
    (Clausification.clausify $ Clausification.skolemize reflexivity)
    @
    (Clausification.clausify $ Clausification.skolemize transitivity)
  in

  let preds = List.filter (function ("=",2) -> false | _ -> true) preds in

  let unique_filter_nonconstant l = 
    List.sort_unique compare l 
    |> List.filter (function (_,0) -> false | _ -> true)
  in

  (equivalence_axioms)
  @
  (List.map axiom_pred @@ unique_filter_nonconstant preds)
  @
  (List.map axiom_func @@ unique_filter_nonconstant funcs)


let axioms l =
  let preds = list_predicates_clauseset l in
  let funcs = list_functions_clauseset l in
  axioms' preds funcs

(* let axioms_int l =
  let preds = list_predicates_clauseset l in
  let funcs = list_functions_clauseset l in
  axioms' preds funcs *)

let has_equality f =
  List.mem ("=",2) (list_predicates_clauseset f)

let add_axioms f = 
  axioms f @ f
