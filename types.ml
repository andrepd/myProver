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
type passignment = bool list list



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
  String.concat ";\n" (List.map string_of_clause x)



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
  String.concat ";\n" (List.map string_of_int_clause x)



let rec string_of_formula x =
  match x with
  | Val true -> "$T"
  | Val false -> "$F"
  | Atom x -> string_of_atom x
  | Not x -> "(NOT " ^ string_of_formula x ^ ")"
  | And (x,y) -> "(AND " ^ string_of_formula x ^ " " ^ string_of_formula y ^ ")"
  | Or  (x,y) -> "(OR " ^ string_of_formula x ^ " " ^ string_of_formula y ^ ")"
  | Imp (x,y) -> "(IMP " ^ string_of_formula x ^ " " ^ string_of_formula y ^ ")"
  | Iff (x,y) -> "(IFF " ^ string_of_formula x ^ " " ^ string_of_formula y ^ ")"
  | Forall (x, p) -> "(FORALL " ^ x ^ " " ^ string_of_formula p ^ ")"
  | Exists (x, p) -> "(EXISTS " ^ x ^ " " ^ string_of_formula p ^ ")"



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



(* let rec compare_lit {sign=s1;lit=l1} {sign=s2;lit=l2} : int =
  s1 = s2 &&  *)
