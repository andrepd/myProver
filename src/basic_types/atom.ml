open Batteries

type 'a t =
	| Pred of 'a * 'a Term.t list

(* type 'a t = 'a atom *)

type 'a atom = 'a t

let to_string inner x =
  match x with 
  | Pred (name, args) -> "(P" ^ inner name ^ " " ^ String.concat " " (List.map (Term.to_string inner) args) ^ ")"

let print inner out x =
  match x with
  | Pred (name, args) -> (
    IO.nwrite out "(P";
    inner out name;
    IO.nwrite out " ";
    List.print ~first:"" ~last:"" ~sep:" " (Term.print inner) out args;
    IO.nwrite out ")";
  )



let subst (s: 'a Subst.fn) (f: 'a atom) =
  match f with
  | Pred (name, args) -> Pred (name, List.map (Term.subst s) args)

let list_functions x =
  match x with
  | Pred (_, args) -> List.concat @@ List.map Term.list_functions args  

let list_predicates x =
  match x with
  | Pred (name, args) -> [name, List.length args]

let list_vars x =
  match x with
  | Pred (_, args) -> Enum.concat_map Term.list_vars (List.enum args)



let rec print_tptp inner out x =
  match x with
  | Pred (name, []) -> 
    (inner out name;)
  | Pred (name, args) ->
    inner out name;
    List.print ~first:"(" ~last:")" ~sep:"," (Term.print_tptp inner) out args  (* can optimise *)

let validate_tptp inner x =
  let valid_functional_ident x = 
    not (String.is_empty x) && Char.is_lowercase x.[0]
  in
  let aux inner x =
    let out_str = IO.output_string() in
    inner out_str x;
    IO.close_out out_str
  in

  match x with
  | Pred (name, args) ->
    (aux inner name |> valid_functional_ident)
    && List.Labels.for_all (Term.validate_tptp inner) args
