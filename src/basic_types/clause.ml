open Batteries

type 'a t = 'a Literal.t list

(* type 'a t = 'a clause *)

type 'a clause = 'a t

let to_string inner x =
  String.concat " , " (List.map (Literal.to_string inner) x)

let print inner out x =
  List.print ~first:"" ~last:"" ~sep:" , " (Literal.print inner) out x

let print_tptp inner out x = 
  failwith "unimplemented"



let subst (s: 'a Subst.fn) (f: 'a clause) =
  List.map (Literal.subst s) f

let list_functions x =
  List.concat @@ List.map (Literal.list_functions) x

let list_predicates x =
  List.concat @@ List.map (Literal.list_predicates) x

let list_vars x =
  Enum.concat_map Literal.list_vars (List.enum x)

let reencode (clause: int clause) : int clause =
  let table_var = ref Map.empty in
  let num_var = ref (-1) in

  let get_num_var (s: int) : int =
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

  let rec encode_term (x: int Term.t) : int Term.t =
    let open Term in
    match x with
    | Var x -> 
      Var (get_num_var x)
    | Func (name, args) ->
      Func (name, List.map encode_term args)
      
  in

  let encode_atom (x: int Atom.t) : int Atom.t =
    let open Atom in
    let Pred (name, args) = x in
    Pred (name, List.map encode_term args)
  in

  List.map (fun ({Literal.sign;Literal.atom}: 'a Literal.t) -> 
    {Literal.sign; Literal.atom = encode_atom atom}
  ) clause

(** Encode a string clause to an int clause *)
let encode table num (clause: 'a clause) : int clause =
  let table_var = ref Map.empty in
  let num_var = ref (-1) in

  let get_num (s: 'a) : int =
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

  let get_num_var (s: 'a) : int =
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

  let rec encode_term (x: 'a Term.t) : int Term.t =
    let open Term in
    match x with
    | Var x -> 
      Var (get_num_var x)
    | Func (name, args) ->
      Func (get_num name, List.map encode_term args)
      
  in

  let encode_atom (x: 'a Atom.t) : int Atom.t =
    let open Atom in
    let Pred (name, args) = x in
    Pred (get_num name, List.map encode_term args)
  in

  List.map (fun {Literal.sign;Literal.atom} -> 
    {Literal.sign; Literal.atom = encode_atom atom}
  ) clause 



let print_tptp ~name ~role inner ~is_infix out x = 
  Printf.fprintf out "cnf(%s,%s,\n" name role;
  List.print
    ~first:  "  ( "
    ~sep:  "\n  | "
    ~last: "\n  )\n"
    (Literal.print_tptp inner ~is_infix) out x;
  IO.nwrite out ")."

let print_tptp_string =
  print_tptp ~is_infix:(fun x -> x = "=")

let validate_tptp inner x =
  List.for_all (Literal.validate_tptp inner) x
