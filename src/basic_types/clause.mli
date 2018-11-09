(** Represents a predicate of 0 or higher arity *)
type 'a t = 'a Literal.t list

(** Representation of a clause *)
val to_string : ('a -> string) -> 'a t -> string  (* lift monad *)

(** Prints representation of a clause to an output*)
val print : 
  ('a BatInnerIO.output -> 'b -> unit) ->
  'a BatInnerIO.output -> 
  'b t -> 
  unit

(* val print_tptp : ('a, 'b) BatIO.printer -> 'a BatIO.output -> 'b t -> unit *)
val print_tptp : name:string -> role:string -> ('a, 'b) BatIO.printer -> is_infix:('a -> bool) -> ('a t, 'b) BatIO.printer
(* val print_tptp_string : name:string -> role:string -> ('a t, 'b) BatIO.printer *)

(** Apply a substitution (mapping of variables to terms) to a clause*)
val subst : ('a -> 'a Term.t) -> 'a t -> 'a t 

(** List of functions (as (name,arity)) in a clause, including duplicates *)
val list_functions : 'a t -> ('a * int) list 

(** List of predicates (as (name,arity)) in a clause, including duplicates *)
val list_predicates : 'a t -> ('a * int) list 

(** List of variables in a clause, including duplicates *)
val list_vars : 'a t -> 'a BatEnum.t

(** Encodes a clause of any type to an int clause *)
val encode : ('a, int) BatMap.t ref -> int ref -> 'a t -> int t

(** Reencodes a clause (specifically, "normalizing" the variables in a consistent manner) *)
val reencode : int t -> int t

(** TPTP *)

(** Validates a term for use with TPTP *)
val validate_tptp : ('a, string) BatIO.printer -> 'a t -> bool
