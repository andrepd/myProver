(** Represents a predicate of 0 or higher arity *)
type 'a t = 'a Clause.t list

(** Representation of a clauseset *)
val to_string : ('a -> string) -> 'a t -> string  (* lift monad *)

(** Prints representation of a clauseset to an output*)
val print : 
  ('a BatInnerIO.output -> 'b -> unit) ->
  'a BatInnerIO.output -> 
  'b t -> 
  unit

val print_tptp : ('a, 'b) BatIO.printer -> is_infix:('a -> bool) -> ('a t, 'b) BatIO.printer
val print_tptp_string : (string t, 'b) BatIO.printer
val to_string_tptp : ('a -> string) -> is_infix:('a -> bool) -> 'a t -> string
val to_string_tptp_string : string t -> string

(** Apply a substitution (mapping of variables to terms) to a clauseset*)
val subst : ('a -> 'a Term.t) -> 'a t -> 'a t 

(** List of functions (as (name,arity)) in a clauseset, including duplicates *)
val list_functions : 'a t -> ('a * int) list 

(** List of predicates (as (name,arity)) in a clauseset, including duplicates *)
val list_predicates : 'a t -> ('a * int) list 

(** Encodes a clauseset of any type to an int clauseset *)
val encode : 'a t -> int t

(** Reencodes a clauseset (specifically, "normalizing" the variables in a consistent manner) *)
val reencode : int t -> int t

(** TPTP *)

(** Validates a term for use with TPTP *)
val validate_tptp : ('a, string) BatIO.printer -> 'a t -> bool
