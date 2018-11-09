open Batteries

type 'a t = {sign: bool; atom: 'a Atom.t}

(* type 'a t = 'a literal *)

type 'a literal = 'a t

let to_string inner {sign;atom} =
  (if sign then "" else "~") ^ Atom.to_string inner atom

let print inner out {sign;atom} =
  if not sign then 
    IO.write out '~';
  Atom.print inner out atom

let print_tptp inner out {sign;atom} =
  failwith "unimplemented"



let subst (s: 'a Subst.fn) ({sign; atom}: 'a literal) = 
  {sign; atom=Atom.subst s atom}

let list_functions {atom} = 
  Atom.list_functions atom

let list_predicates {atom} = 
  Atom.list_predicates atom

let list_vars {atom} =
  Atom.list_vars atom



let print_tptp inner ~is_infix out {sign;atom} =
  match atom with
  | Pred (name, args) ->
    (* Infix predicate *)
    if is_infix name then (
      begin match args with
      | [lhs;rhs] ->
        if sign then (
          Term.print_tptp inner out lhs;
          IO.nwrite out " = ";
          Term.print_tptp inner out rhs;
        ) else (
          Term.print_tptp inner out lhs;
          IO.nwrite out " != ";
          Term.print_tptp inner out rhs;
        )
      | _ -> failwith "print_tptp: equality predicate arity different from 2"
      end
    )
    (* Regular predicate *)
    else (
      if not sign then 
        IO.write out '~';
      Atom.print_tptp inner out atom
    )

let validate_tptp inner {sign;atom} =
  Atom.validate_tptp inner atom
