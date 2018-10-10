open Batteries

open Debug

type 'a fn = 'a -> 'a Term.t

type 'a map = ('a, 'a Term.t) Map.t

let map_to_func (env: ('a, 'a Term.t) Map.t) : ('a -> 'a Term.t) = 
  fun x -> Map.find_default (Term.Var x) x env

let (>=>) (a: 'a fn) (b: 'a fn) =
  a %> (function               
    Term.Var x -> b x | Term.Func _ -> failwith "substitutions cannot be composed")

(* let bind = (>>=) *)

let to_string inner (s: 'a map) =
  let pair_to_string inner (a,b) = 
    inner a ^ "/" ^ Term.to_string inner b
  in
  String.concat ", " (List.of_enum @@ map (pair_to_string inner) (Map.enum s))

let print inner out (s: 'a map) =
  let pair_print inner out ((a,b): 'a * 'a Term.t) =
    (* print inner out a; *)
    inner out a;
    IO.write out '/';
    Term.print inner out b
  in
  Enum.print ~first:"" ~last:"" ~sep:"/" (pair_print inner) out (Map.enum s)
