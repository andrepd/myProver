open Batteries

open Types
open Util

open Debug

let contig_vars n = 
  Char.range 'a'
  |> Enum.take n
  |> map (fun x -> Var (Char.escaped x))
  |> List.of_enum

let axioms (preds: ('a * int) list) (funcs: ('a * int) list) : 'a clauseset =
  (* Equality axiom for a function *)
  let axiom_func ((name,arity): ('a * int)) : 'a clause =
    let f_left n = {sign=false; lit=Pred ("=", [
      Var ("x"^string_of_int n);
      Var ("y"^string_of_int n)
    ])} in
    let f_right x n = Var (x ^ string_of_int n) in

    let left = List.init arity f_left in
    let right = {sign=true; lit=Pred ("=", [
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
  let axiom_pred ((name,arity): ('a * int)) : 'a clause =
    let f_left n = {sign=false; lit=Pred ("=", [
      Var ("x"^string_of_int n);
      Var ("y"^string_of_int n)
    ])} in
    let f_right x n = Var (x ^ string_of_int n) in

    let left = List.init arity f_left in
    let right = [
      {sign=false; lit=Pred (name, List.init arity (f_right "x"))};
      {sign=true;  lit=Pred (name, List.init arity (f_right "y"))};
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
    let transitifity = 
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
    (Clausification.clausify $ Clausification.skolemize transitifity)
  in

  let preds = List.filter (fun (name,_) -> name <> "=") preds in
  (equivalence_axioms)
  @
  (List.map axiom_pred (List.sort_unique compare preds |> List.filter (fun (_,arity) -> arity <> 0)))
  @
  (List.map axiom_func (List.sort_unique compare funcs |> List.filter (fun (_,arity) -> arity <> 0)))


let axioms_string l =
  let preds = list_predicates_clauseset l in
  let funcs = list_functions_clauseset l in
  axioms preds funcs

(* let axioms_int l =
  let preds = list_predicates_clauseset l in
  let funcs = list_functions_clauseset l in
  axioms preds funcs *)
