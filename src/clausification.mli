open Types

val clausify : 'a formula -> 'a clauseset
(** Turns a FOL formula into a clause set *)
(* val clausify_opt : 'a formula -> 'a clauseset *)

val skolemize : string formula -> string formula
(** Removes quantifiers via Skolemization *)
