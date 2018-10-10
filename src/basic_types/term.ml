open Batteries

open Debug

type 'a t = 
  | Var of 'a
  | Func of 'a * 'a t list

(* type 'a t = 'a term *)

type 'a term = 'a t

let rec to_string inner x = 
  match x with
  | Var x -> "v" ^ (inner x)
  | Func (name, args) -> "(F" ^ inner name ^ " " ^ String.concat " " (List.map (to_string inner) args) ^ ")"

let rec print inner out x =
  match x with
  | Var x -> (
    IO.write out 'v';
    inner out x;
  )
  | Func (name, args) -> (
    IO.nwrite out "(F";
    inner out name;
    IO.nwrite out " ";
    List.print ~first:"" ~last:"" ~sep:" " (print inner) out args;
    IO.nwrite out ")";
  )



type 'a subst = 'a -> 'a term

let rec subst (s: 'a subst) (f: 'a term) =
  match f with
  | Var x -> s x
  | Func (name, args) -> Func (name, List.map (subst s) args)

let rec list_functions (t: 'a term) : ('a * int) list =
  match t with
  | Var x -> []
  | Func (name, args) -> (name, List.length args) :: (List.concat @@ List.map list_functions args)

let rec list_vars x =
  match x with
  | Var y -> Enum.singleton y
  | Func (_, args) -> Enum.concat_map list_vars (List.enum args)



let rec print_tptp inner out x =
  (* let valid_variable_ident x = 
    not (String.is_empty x) && Char.is_uppercase x.[0]
  in
  let valid_functional_ident x = 
    not (String.is_empty x) && Char.is_lowercase x.[0]
  in
  let aux x =
    let out_str = IO.output_string() in
    inner out_str x;
    IO.close_out out_str
  in *)
  
  match x with
  | Var x -> (
    (* let x = IO.read_all (inner x ()) in *)
    (* let x = IO.to_string inner x in *)
    (* let 
    if not (valid_variable_ident x) then
      failwith @@ Printf.sprintf "invalid var identifier `%s`" x; *)
    inner out x
  ) | Func (name, []) -> (
    inner out name
  ) | Func (name, args) -> (
    (* let name = IO.read_all (inner name ()) *)
    (* let name = IO.to_string inner name in *)
    (* let 
    if not (valid_functional_ident name) then
      failwith @@ Printf.sprintf "invalid func identifier `%s`" name; *)
    inner out name;
    IO.write out '(';
    List.print ~first:"" ~last:"" ~sep:"," (print_tptp inner) out args;  (* can optimise *)
    IO.write out ')';
  )

let rec validate_tptp inner x =
  let valid_variable_ident x = 
    not (String.is_empty x) && Char.is_uppercase x.[0]
  in
  let valid_functional_ident x = 
    not (String.is_empty x) && Char.is_lowercase x.[0]
  in
  let aux inner x =
    let out_str = IO.output_string() in
    inner out_str x;
    IO.close_out out_str
  in

  match x with
  | Var x -> (
    aux inner x |> valid_variable_ident
  ) | Func (name, args) -> (
    (aux inner name |> valid_functional_ident)
    && List.Labels.for_all (validate_tptp inner) args
  )
