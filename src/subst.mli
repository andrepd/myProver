type 'a fn = 'a -> 'a Term.t

type 'a map = ('a, 'a Term.t) BatMap.t

val map_to_func : 'a map -> 'a fn

val (>=>) : 'a fn -> 'a fn -> 'a fn

(** Representation of a clauseset *)
val to_string : ('a -> string) -> 'a map -> string  (* lift monad *)

(** Prints representation of a clauseset to an output*)
val print : 
  ('a BatInnerIO.output -> 'b -> unit) ->
  'a BatInnerIO.output -> 
  'b map -> 
  unit
