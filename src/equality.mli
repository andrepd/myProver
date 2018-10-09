open Types

(* val axioms_string : string clauseset -> string clauseset *)
val axioms : string clauseset -> string clauseset
(** Returns the equality axioms for a given formula *)

val add_axioms : string clauseset -> string clauseset
(** Adds the equality axioms for a given formula (axioms ++ original) *)

(* val add_axioms_if_equality : string clauseset -> string clauseset *)
(** Adds the equality axioms for a given formula IF it has the equality predicate *)

(* val axioms_int : int clauseset -> int clauseset
(** Returns the equality axioms for a given formula *) *)

val has_equality : string clauseset -> bool
(** Checks if formula has equality predicates *)

