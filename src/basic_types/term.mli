(** Represents a term: a variable, or a function of 0 or higher arity *)
type 'a t = 
  | Var of 'a
  | Func of 'a * 'a t list

(** S-expression representation of a term *)
val to_string : ('a -> string) -> 'a t -> string  (* lift monad *)

(** Prints s-expression representation of a term to an output*)
val print : 
  ('a BatInnerIO.output -> 'b -> unit) ->
  'a BatInnerIO.output -> 
  'b t -> 
  unit

val print_tptp : ('a, 'b) BatIO.printer -> 'b BatIO.output -> 'a t -> unit

(** Apply a substitution (mapping of variables to terms) to a term*)
val subst : ('a -> 'a t) -> 'a t -> 'a t 

(** List of functions (as (name,arity)) in a term, including duplicates *)
val list_functions : 'a t -> ('a * int) list 

(** List of variables in a term, including duplicates *)
val list_vars : 'a t -> 'a BatEnum.t

(** TPTP *)

(** Validates a term for use with TPTP *)
val validate_tptp : ('a, string) BatIO.printer -> 'a t -> bool
