(** Represents a predicate of 0 or higher arity *)
type 'a t = 
  {sign: bool; atom: 'a Atom.t}

(** S-expression representation of a literal *)
val to_string : ('a -> string) -> 'a t -> string  (* lift monad *)

(** Prints s-expression representation of a literal to an output*)
val print : 
  ('a BatInnerIO.output -> 'b -> unit) ->
  'a BatInnerIO.output -> 
  'b t -> 
  unit

val print_tptp : ('a, 'b) BatIO.printer -> is_infix:('a -> bool) -> 'b BatIO.output -> 'a t -> unit

(** Apply a substitution (mapping of variables to terms) to a literal*)
val subst : ('a -> 'a Term.t) -> 'a t -> 'a t 

(** List of functions (as (name,arity)) in a literal, including duplicates *)
val list_functions : 'a t -> ('a * int) list 

(** List of predicates (as (name,arity)) in a literal, including duplicates *)
val list_predicates : 'a t -> ('a * int) list 

(** List of variables in a literal, including duplicates *)
val list_vars : 'a t -> 'a BatEnum.t

(** TPTP *)

(** Validates a term for use with TPTP *)
val validate_tptp : ('a, string) BatIO.printer -> 'a t -> bool
