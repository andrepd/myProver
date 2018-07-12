type 'a term = 
	| Var of 'a
	| Func of 'a * 'a term list

type 'a atom =
	| Pred of 'a * 'a term list

type 'a formula =
	| Val of bool
	| Atom of 'a atom
  | Not of 'a formula (* Faltava *)
	| And of 'a formula * 'a formula
	| Or  of 'a formula * 'a formula
	| Imp of 'a formula * 'a formula
	| Iff of 'a formula * 'a formula
	| Forall of 'a * 'a formula
	| Exists of 'a * 'a formula

type 'a literal = {sign: bool; lit: 'a atom}
type 'a clause = 'a literal list
type 'a clauseset = 'a clause list

type pmodel = bool array



let string_of_atom x =
  let rec string_of_term x = 
    match x with
    | Var x -> "V"^x
    | Func (name, args) -> "(F" ^ name ^ " " ^ String.concat " " (List.map string_of_term args) ^ ")"
  in
  let Pred (name, args) = x in
  "(P" ^ name ^ " " ^ String.concat " " (List.map string_of_term args) ^ ")"

let string_of_literal {sign;lit} =
  (if sign then "" else "~") ^ string_of_atom lit

let string_of_clause x =
  String.concat " , " (List.map string_of_literal x)

let string_of_clauseset x =
  String.concat "\n" (List.map string_of_clause x)



let string_of_int_atom x =
  let rec string_of_int_term x = 
    match x with
    | Var x -> "V" ^ BatInt.to_string x
    | Func (name, args) -> "(F" ^ BatInt.to_string name ^ " " ^ String.concat " " (List.map string_of_int_term args) ^ ")"
  in
  let Pred (name, args) = x in
  "(P" ^ BatInt.to_string name ^ " " ^ String.concat " " (List.map string_of_int_term args) ^ ")"

let string_of_int_literal {sign;lit} =
  (if sign then "" else "~") ^ string_of_int_atom lit

let string_of_int_clause x =
  String.concat " , " (List.map string_of_int_literal x)

let string_of_int_clauseset x =
  String.concat "\n" (List.map string_of_int_clause x)
