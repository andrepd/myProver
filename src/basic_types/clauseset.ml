open Batteries

type 'a t = 'a Clause.t list

(* type 'a t = 'a clauseset *)

type 'a clauseset = 'a t

let to_string inner x =
  String.concat ";\n" (List.map (Clause.to_string inner) x)

let print inner out x =
  (* List.print ~first:"" ~last:"" ~sep:";\n" inner out x *)
  List.print ~first:"" ~last:"" ~sep:";\n" (Clause.print inner) out x



let subst (s: 'a -> 'a Term.t) (f: 'a clauseset) =
  List.map (Clause.subst s) f

let list_functions (x: 'a clauseset) : ('a * int) list =
  (* List.sort_unique compare @@ *)
  List.concat @@ List.map (Clause.list_functions) x

let list_predicates (x: 'a clauseset) : ('a * int) list =
  (* List.sort_unique compare @@ *)
  List.concat @@ List.map (Clause.list_predicates) x

let encode x = 
  let table = ref Map.empty in
  let num = ref 1 in
  List.map (Clause.encode table num) x

let reencode x = 
  List.map (Clause.reencode) x



let print_tptp inner out x =
  List.print ~first:"" ~last:"" ~sep:"\n\n" (Clause.print_tptp ~name:"test" ~role:"axiom" inner) out x

let validate_tptp inner x =
  List.for_all (Clause.validate_tptp inner) x
