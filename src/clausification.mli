open Types

val clausify : 'a formula -> 'a clauseset
(** Turns a FOL formula into a clause set *)
(* val clausify_opt : 'a formula -> 'a clauseset *)

val skolemize : variant:(string -> string list -> string) -> string formula -> string formula
(** Removes quantifiers via Skolemization *)

val skolemize_string : string formula -> string formula
(** As [skolemize ~variant:(Util.variant_string)] *)