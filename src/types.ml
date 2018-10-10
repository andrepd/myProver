open Batteries

type 'a term = 'a Term.t =
  | Var of 'a
  | Func of 'a * 'a term list

type 'a atom = 'a Atom.t =
  | Pred of 'a * 'a Term.t list

type 'a formula = 'a Formula.t =
  | Val of bool
  | Atom of 'a Atom.t
  | Not of 'a formula
  | And of 'a formula * 'a formula
  | Or  of 'a formula * 'a formula
  | Imp of 'a formula * 'a formula
  | Iff of 'a formula * 'a formula
  | Forall of 'a * 'a formula
  | Exists of 'a * 'a formula

type 'a literal = 'a Literal.t = 
  {sign: bool; atom: 'a Atom.t}

type 'a clause = 'a Clause.t
  (* = 'a Literal.t list) *)

type 'a clauseset = 'a Clauseset.t 
  (* = 'a Clause.t list *)


let string_of_term x = Term.to_string identity x

let string_of_atom x = Atom.to_string identity x

let string_of_literal x = Literal.to_string identity x

let string_of_clause x = Clause.to_string identity x

let string_of_clauseset x = Clauseset.to_string identity x


let string_of_int_term x = Term.to_string Int.to_string x

let string_of_int_atom x = Atom.to_string Int.to_string x

let string_of_int_literal x = Literal.to_string Int.to_string x

let string_of_int_clause x = Clause.to_string Int.to_string x

let string_of_int_clauseset x = Clauseset.to_string Int.to_string x


let rec string_of_formula x = Formula.to_string identity x

let rec string_of_int_formula x = Formula.to_string Int.to_string x



let rec prettyprint_of_term x =
  match x with
  | Var x -> x
  | Func (name, args) -> name ^ "(" ^ String.concat "," (List.map prettyprint_of_term args) ^ ")"

let rec prettyprint_of_atom x =
  let Pred (name, args) = x in
  name ^ "(" ^ String.concat "," (List.map prettyprint_of_term args) ^ ")"

let rec prettyprint_of_formula f =
  match f with
  | Val true -> "T"
  | Val false -> "F"
  | Atom x -> prettyprint_of_atom x
  | Not x -> "~" ^ prettyprint_of_formula x
  | And (x,y) -> (
    let rec aux a = 
      match a with
      | And (z,w) -> aux z @ aux w
      | _ -> [a]
    (* in "(" ^ prettyprint_of_formula x ^ " & "  ^ prettyprint_of_formula y ^ ")" *)
    in "(" ^ String.concat " & " (List.map prettyprint_of_formula (aux x @ aux y)) ^ ")"
  )
  | Or  (x,y) -> (
    let rec aux a = 
      match a with
      | Or (z,w) -> aux z @ aux w
      | _ -> [a]
    (* in "(" ^ prettyprint_of_formula x ^ " | "  ^ prettyprint_of_formula y ^ ")" *)
    in "(" ^ String.concat " | " (List.map prettyprint_of_formula (aux x @ aux y)) ^ ")"
  )
  | Imp (x,y) -> "(" ^ prettyprint_of_formula x ^ " => " ^ prettyprint_of_formula y ^ ")"
  | Iff (x,y) -> "(" ^ prettyprint_of_formula x ^ " == " ^ prettyprint_of_formula y ^ ")"
  (* | Forall (x, p) -> "(@"  ^ x ^ ". " ^ prettyprint_of_formula p ^ ")"
  | Exists (x, p) -> "(\\" ^ x ^ ". " ^ prettyprint_of_formula p ^ ")" *)
  | Forall (x, p) -> (
    let rec aux names formula =
      match formula with
      | Forall (x, p) -> aux (x::names) p
      | _ -> (names, formula)
    in
    let names, formula = aux [] f in
    "(@"  ^ String.concat " " (List.rev names)  ^ ". " ^ prettyprint_of_formula formula ^ ")"
  )
  | Exists (x, p) -> (
    let rec aux names formula =
      match formula with
      | Exists (x, p) -> aux (x::names) p
      | _ -> (names, formula)
    in
    let names, formula = aux [] f in
    "(\\" ^ String.concat " " (List.rev names)  ^ ". " ^ prettyprint_of_formula formula ^ ")"
  )



(* let rec compare_lit {sign=s1;atom=l1} {sign=s2;atom=l2} : int =
  s1 = s2 &&  *)
